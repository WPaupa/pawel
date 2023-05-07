module Inference where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import qualified Text.PrettyPrint as PP
import AbsPawel

data Scheme  =  Scheme [Idt] Type deriving (Eq,Show)

class Types a where
    ftv    ::  a -> Set.Set Idt
    apply  ::  Subst -> a -> a

instance Types Type where
    ftv (TVar n)      =  Set.singleton n
    ftv TInt          =  Set.empty
    ftv (TFunc t1 t2)  =  ftv t1 `Set.union` ftv t2
    ftv (TVariant name types) = Set.unions $ map ftv types
    apply s (TVar n)      =  case Map.lookup n s of
                               Nothing  -> TVar n
                               Just t   -> t
    apply s (TFunc t1 t2)  = TFunc (apply s t1) (apply s t2)
    apply s (TVariant name types) = TVariant name (map (apply s) types)
    apply s t             =  t

instance Types Scheme where
    ftv (Scheme vars t)      =  (ftv t) `Set.difference` (Set.fromList vars)
    apply s (Scheme vars t)  =  Scheme vars (apply (foldr Map.delete s vars) t)

instance Types a => Types [a] where
    apply s  =  map (apply s)
    ftv l    =  foldr Set.union Set.empty (map ftv l)

type Subst = Map.Map Idt Type
nullSubst  ::  Subst
nullSubst  =   Map.empty
composeSubst         :: Subst -> Subst -> Subst
composeSubst s1 s2   = (Map.map (apply s1) s2) `Map.union` s1

newtype TypeEnv = TypeEnv (Map.Map Idt Scheme)

remove                    ::  TypeEnv -> Idt -> TypeEnv
remove (TypeEnv env) var  =  TypeEnv (Map.delete var env)
instance Types TypeEnv where
    ftv (TypeEnv env)      =  ftv (Map.elems env)
    apply s (TypeEnv env)  =  TypeEnv (Map.map (apply s) env)

generalize        ::  TypeEnv -> Type -> Scheme
generalize env t  =   Scheme vars t
  where vars = Set.toList ((ftv t) `Set.difference` (ftv env))

data TIEnv = TIEnv  {}
data TIState = TIState { tiSupply :: Int }
type TI a = ErrorT String (ReaderT TIEnv (StateT TIState IO)) a
runTI :: TI a -> IO (Either String a, TIState)
runTI t = 
    do (res, st) <- runStateT (runReaderT (runErrorT t) initTIEnv) initTIState
       return (res, st)
  where initTIEnv = TIEnv
        initTIState = TIState{tiSupply = 0}
newTyVar :: String -> TI Type
newTyVar prefix =
    do  s <- get
        put s{tiSupply = tiSupply s + 1}
        return (TVar $ Idt (prefix ++ show (tiSupply s)))

newVar :: String -> TI Idt
newVar prefix =
    do  s <- get
        put s{tiSupply = tiSupply s + 1}
        return (Idt (prefix ++ show (tiSupply s)))

instantiate :: Scheme -> TI Type
instantiate (Scheme vars t) = do  nvars <- mapM (\ _ -> newTyVar "a") vars
                                  let s = Map.fromList (zip vars nvars)
                                  return $ apply s t

mgu :: Type -> Type -> TI Subst
mgu (TFunc l r) (TFunc l' r')    =  do  s1 <- mgu l l'
                                        s2 <- mgu (apply s1 r) (apply s1 r')
                                        return (s1 `composeSubst` s2)
mgu (TVar u) t                 =  varBind u t
mgu t (TVar u)                 =  varBind u t
mgu TInt TInt                  =  return nullSubst
mgu TInt (TFunc (TInt) b)      =  throwError $ "TypeError, expected Int, got Int -> " ++ show b
mgu TInt (TFunc (TFunc t1 t2) b) =  do  s1 <- mgu (TFunc t1 t2) b
                                        s2 <- mgu (apply s1 t1) (apply s1 t2)
                                        return (s1 `composeSubst` s2)
mgu TInt (TFunc (TVar a) b)    =  mgu (TVar a) b
mgu t1 TInt                    =  mgu TInt t1
mgu (TVariant (Idt name) types) (TVariant (Idt name') types') 
    | name == name' = foldM (\s (t1, t2) -> do {s1 <- mgu t1 t2; return (s `composeSubst` s1)}) nullSubst (zip types types')
    | otherwise = throwError $ "TypeError, expected " ++ name ++ ", got " ++ name'
mgu (TVariant name types) (TFunc t1 t2) = throwError "TypeError: variant application not yet implemented"
mgu t1 t2                      =  throwError $ "types do not unify: " ++ show t1 ++ 
                                  " vs. " ++ show t2

haveItBeInt :: Type -> TI Subst
haveItBeInt (TInt) = return nullSubst
haveItBeInt (TVar a) = return $ Map.singleton a TInt
haveItBeInt t = throwError $ "TypeError, expected Int, got " ++ show t

varBind :: Idt -> Type -> TI Subst
varBind u t  | t == TVar u           =  return nullSubst
             | otherwise             =  return (Map.singleton u t)


ti        ::  TypeEnv -> ExpBound -> TI (Subst, Type)
ti (TypeEnv env) (EBVar n@(Idt n')) = 
    case Map.lookup n env of
       Nothing     ->  throwError $ "unbound variable: " ++ n'
       Just sigma  ->  do  t <- instantiate sigma
                           return (nullSubst, t)
ti (TypeEnv env) (EOVar pos n@(Idt n')) = 
    case Map.lookup n env of
       Nothing     ->  throwError $ "unbound variable: " ++ n'
       Just sigma  ->  do  t <- instantiate sigma
                           return (nullSubst, t)
ti _ (EBInt n) = (return (nullSubst, TInt))
ti env (EBVariant name es) = -- TODO dostawanie środowiska z konstruktorami
    let f (s, ts) e = do {
        (s', t') <- ti (apply s env) e;
        return (s' `composeSubst` s, (t':ts))
     } in
    foldM f (nullSubst, []) es >>= \(s, ts) -> return (s, TVariant name $ reverse ts)
ti (TypeEnv env) (EBCons (FWCons f)) = do
    v <- newVar "a"
    tv <- newTyVar "a"
    let env' = TypeEnv (env `Map.union` (Map.singleton v (Scheme [] tv)))
    (s1, t1) <- ti env' (f $ EBVar v)
    return (s1, TFunc (apply s1 tv) t1)
ti env (EBIf e1 e2 e3) = do
    (s1, t1) <- ti env e1
    s2 <- haveItBeInt (apply s1 t1) 
    (s3, t2) <- ti (apply (s2 `composeSubst` s1) env) e2
    (s4, t3) <- ti (apply (s3 `composeSubst` s2 `composeSubst` s1) env) e3
    s5 <- mgu (apply (s4 `composeSubst` s3 `composeSubst` s2 `composeSubst` s1) t2) (apply (s4 `composeSubst` s3 `composeSubst` s2 `composeSubst` s1) t3)
    return (s5 `composeSubst` s4 `composeSubst` s3 `composeSubst` s2 `composeSubst` s1, apply s5 t2)
ti env (EBLet x tds e1 e2) =
    do  (s1, t1) <- ti env (EBLam Map.empty (map untype tds) e1) -- środowisko
        let TypeEnv env' = remove env x
            t' = generalize (apply s1 env) t1
            env'' = TypeEnv (Map.insert x t' env')
        (s2, t2) <- ti (apply s1 env'') e2
        return (s1 `composeSubst` s2, t2)
ti env (EBLam lenv [] e) = ti env e
ti env (EBLam lenv (n:t) e) =
    do  tv <- newTyVar "a"
        let TypeEnv env' = remove env n
            env'' = TypeEnv (env' `Map.union` (Map.singleton n (Scheme [] tv)))
        (s1, t1) <- ti env'' (EBLam lenv t e)
        return (s1, TFunc (apply s1 tv) t1)
ti env (EBMatch x cases) = -- TODO dostawanie środowiska z konstruktorami
    let f (s, t) (CaseBound match e) = do {
        (s', t') <- ti (apply s env) e;
        case t of
            Nothing -> return (s', Just t')
            Just t'' -> do 
                s'' <- mgu (apply s' t'') (apply s' t')
                return (s'' `composeSubst` s' `composeSubst` s, Just $ apply s'' t'');
     } in
    foldM f (nullSubst, Nothing) cases >>= \(s, Just t) -> return (s, t)
ti env exp@(EBApp e1 e2) =
    do  tv <- newTyVar "a"
        (s1, t1) <- ti env e1
        (s2, t2) <- ti (apply s1 env) e2
        s3 <- mgu (apply s2 t1) (TFunc t2 tv)
        return (s3 `composeSubst` s2 `composeSubst` s1, apply s3 tv)
    `catchError`
    \e -> throwError $ e ++ "\n in " ++ show exp
ti env (EBArith e1 e2 op) = 
    do  (s1, t1) <- ti env e1
        (s2, t2) <- ti (apply s1 env) e2
        s3 <- haveItBeInt (apply (s2 `composeSubst` s1) t1) 
        s4 <- haveItBeInt (apply (s3 `composeSubst` s2 `composeSubst` s1) t2)
        return (s4 `composeSubst` s3 `composeSubst` s2 `composeSubst` s1, TInt)


typeInference :: Map.Map Idt Scheme -> ExpBound -> TI Type
typeInference env e =
    do  (s, t) <- ti (TypeEnv env) e
        return (apply s t)
       
test :: ExpBound -> IO ()
test e =
    do  (res, _) <- runTI (typeInference Map.empty e)
        case res of
          Left err  ->  putStrLn $ show e ++ "\n " ++ err ++ "\n"
          Right t   ->  putStrLn $ show e ++ " :: " ++ show t ++ "\n"