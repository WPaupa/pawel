module Inference where

import AbsPawel
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set
import MatchChecker
import qualified Text.PrettyPrint as PP

class Types a where
    ftv :: a -> Set.Set Idt
    apply :: Subst -> a -> a

instance Types Type where
    ftv (TVar n) = Set.singleton n
    ftv TInt = Set.empty
    ftv (TFunc t1 t2) = ftv t1 `Set.union` ftv t2
    ftv (TVariant name types) = Set.unions $ map ftv types
    ftv (TOverload types) = Set.unions $ map ftv types
    apply s (TVar n) = case Map.lookup n s of
        Nothing -> TVar n
        Just t -> t
    apply s (TFunc t1 t2) = TFunc (apply s t1) (apply s t2)
    apply s (TVariant name types) = TVariant name (map (apply s) types)
    apply s (TOverload types) = TOverload (map (apply s) types)
    apply s t = t

instance Types Scheme where
    ftv (Scheme vars t) = (ftv t) `Set.difference` (Set.fromList vars)
    apply s (Scheme vars t) = Scheme vars (apply (foldr Map.delete s vars) t)

instance (Types a) => Types [a] where
    apply s = map (apply s)
    ftv l = foldr Set.union Set.empty (map ftv l)

type Subst = Map.Map Idt Type
nullSubst :: Subst
nullSubst = Map.empty
composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = (Map.map (apply s1) s2) `Map.union` s1

remove :: TypeEnv -> Idt -> TypeEnv
remove (TypeEnv env) var = TypeEnv (Map.delete var env)
instance Types TypeEnv where
    ftv (TypeEnv env) = ftv (Map.elems env)
    apply s (TypeEnv env) = TypeEnv (Map.map (apply s) env)

generalize :: TypeEnv -> Type -> Scheme
generalize env t = Scheme vars t
  where
    vars = Set.toList ((ftv t) `Set.difference` (ftv env))

unfunify :: Type -> Type
unfunify (TFunc t1 t2) = unfunify t2
unfunify t = t

data TIState = TIState {tiSupply :: Int}
type TI a = ExceptT String (ReaderT VariantEnv (State TIState)) a
runTI :: VariantEnv -> TI a -> (Either String a, TIState)
runTI env t = runState (runReaderT (runExceptT t) env) $ TIState{tiSupply = 0}

newTyVar :: String -> TI Type
newTyVar prefix =
    do
        s <- get
        put s{tiSupply = tiSupply s + 1}
        return (TVar $ Idt (prefix ++ show (tiSupply s)))

instantiate :: Scheme -> TI Type
instantiate (Scheme vars t) = do
    nvars <- mapM (\_ -> newTyVar "a") vars
    let s = Map.fromList (zip vars nvars)
    return $ apply s t

mgu :: Type -> Type -> TI Subst
mgu (TFunc l r) (TFunc l' r') = do
    s1 <- mgu l l'
    s2 <- mgu (apply s1 r) (apply s1 r')
    return (s1 `composeSubst` s2)
mgu (TVar u) t = varBind u t
mgu t (TVar u) = varBind u t
mgu TInt TInt = return nullSubst
mgu TInt (TFunc (TInt) b) = throwError $ "TypeError, expected Int, got Int -> " ++ show b
mgu TInt (TFunc (TFunc t1 t2) b) = do
    s1 <- mgu (TFunc t1 t2) b
    s2 <- mgu (apply s1 t1) (apply s1 t2)
    return (s1 `composeSubst` s2)
mgu TInt (TFunc (TVar a) b) = mgu (TVar a) b
mgu t1 TInt = mgu TInt t1
mgu (TVariant name types) (TVariant name' types')
    | (length types == length types') && (name == name') =
        foldM
            ( \s (t1, t2) -> do
                s1 <- mgu t1 t2
                return (s `composeSubst` s1)
            )
            nullSubst
            (zip types types')
    | otherwise =
        throwError $
            "TypeError, variant types "
                ++ show name
                ++ "("
                ++ (show $ length types)
                ++ ") and "
                ++ show name'
                ++ "("
                ++ (show $ length types')
                ++ ") do not match"
mgu (TVariant name types) (TFunc t1 t2) = throwError "TypeError: variant application not yet implemented"
mgu t1 t2 =
    throwError $
        "types do not unify: "
            ++ show t1
            ++ " vs. "
            ++ show t2

haveItBeInt :: Type -> TI Subst
haveItBeInt (TInt) = return nullSubst
haveItBeInt (TVar a) = return $ Map.singleton a TInt
haveItBeInt t = throwError $ "TypeError, expected Int, got " ++ show t

varBind :: Idt -> Type -> TI Subst
varBind u t
    | t == TVar u = return nullSubst
    | u `Set.member` ftv t =
        throwError $
            "occurs check fails: "
                ++ (show u)
                ++ " vs. "
                ++ show t
    | otherwise = return (Map.singleton u t)

freshVariantType :: Idt -> Int -> TI Type
freshVariantType name n = do
    vars <- mapM (\_ -> newTyVar "a") [1 .. n]
    return $ TVariant name vars

ti :: TypeEnv -> ExpBound -> TI (Subst, Type)
ti (TypeEnv env) (EBVar n) =
    case Map.lookup n env of
        Nothing -> throwError $ "unbound variable: " ++ (show n)
        Just sigma -> do
            t <- instantiate sigma
            return (nullSubst, t)
ti (TypeEnv env) (EOVar pos n) =
    case Map.lookup n env of
        Nothing -> throwError $ "unbound variable: " ++ (show n)
        Just sigma -> do
            t <- instantiate sigma
            case t of
                TOverload ts -> return (nullSubst, ts !! pos)
                _ -> throwError $ "expected overloaded type, got " ++ show t
ti _ (EBInt n) = (return (nullSubst, TInt))
ti env@(TypeEnv env') (EBVariant name es) =
    let f (s, ts) e = do
            (s', t') <- ti (apply s env) e
            return (s' `composeSubst` s, (t' : ts))
     in case Map.lookup name env' of
            Nothing -> throwError $ "unbound variant constructor: " ++ show name
            Just sigma -> do
                t <- instantiate sigma
                case unfunify t of
                    (TVariant name' ts') -> do
                        (s, ts) <- foldM f (nullSubst, []) es
                        s' <- mgu (TVariant name ts) (unfunify t)
                        return (s' `composeSubst` s, apply s' (unfunify t))
                    _ -> throwError $ "expected variant constructor, got " ++ show (unfunify t)
ti env (EBIf e1 e2 e3) = do
    (s1, t1) <- ti env e1
    s2 <- haveItBeInt (apply s1 t1)
    (s3, t2) <- ti (apply (s2 `composeSubst` s1) env) e2
    (s4, t3) <- ti (apply (s3 `composeSubst` s2 `composeSubst` s1) env) e3
    s5 <-
        mgu
            (apply (s4 `composeSubst` s3 `composeSubst` s2 `composeSubst` s1) t2)
            (apply (s4 `composeSubst` s3 `composeSubst` s2 `composeSubst` s1) t3)
    return (s5 `composeSubst` s4 `composeSubst` s3 `composeSubst` s2 `composeSubst` s1, apply s5 t3)
ti env (EBLet x tds e1 e2) = do
    (s1, t1) <- ti env (EBLam Map.empty (map untype tds) e1)
    let typeof [] = newTyVar "a"
        typeof ((TDVar x) : t) = do
            tv <- newTyVar "a"
            t' <- typeof t
            return $ TFunc tv t'
        typeof ((TDType x typ) : t) = do
            t' <- typeof t
            return $ TFunc typ t'
    t <- typeof tds
    s' <- mgu t1 t
    let TypeEnv env' = remove env x
        t' = generalize (apply (s' `composeSubst` s1) env) (apply s' t1)
        env'' = TypeEnv (Map.insert x t' env')

    (s2, t2) <- ti (apply (s' `composeSubst` s1) env'') e2
    return (s2 `composeSubst` s' `composeSubst` s1, t2)
ti env (EBLam lenv [] e) = ti env e
ti env (EBLam lenv (n : t) e) =
    do
        tv <- newTyVar "a"
        let TypeEnv env' = remove env n
            env'' = TypeEnv (env' `Map.union` (Map.singleton n (Scheme [] tv)))
        (s1, t1) <- ti env'' (EBLam lenv t e)
        return (s1, TFunc (apply s1 tv) t1)
ti env@(TypeEnv env') (EBMatch x cases) =
    let consargs (TFunc t1 t2) = t1 : (consargs t2)
        consargs _ = []
        getTypeAndUnify match typ = case Map.lookup match env' of
            Nothing -> throwError $ "unbound variant constructor: " ++ show match
            Just sigma -> do
                t <- instantiate sigma
                case unfunify t of
                    (TVariant name ts) -> fmap (\x -> ((consargs t), x)) (mgu (unfunify t) typ)
                    _ -> throwError $ "expected variant constructor, got " ++ show (unfunify t)
        doMatch (MVar n) (TypeEnv env) xtype =
            return (nullSubst, TypeEnv (Map.insert n (Scheme [] xtype) env))
        doMatch (MCons name ms) (TypeEnv env) xtype = case xtype of
            TFunc _ _ -> throwError $ "expected variant type, got " ++ show xtype
            _ -> do
                (ts, s) <- getTypeAndUnify name xtype
                foldM
                    (\(s, e) (m, t) -> do (s', e') <- doMatch m e (apply s t); return (s' `composeSubst` s, e'))
                    (s, apply s (TypeEnv env))
                    (zip ms ts)
        f (xtype, s, t) (CaseBound match e) = do
            (sE, mEnv) <- doMatch match (apply s env) xtype
            (s', t') <- ti mEnv e
            let s'' = s' `composeSubst` sE `composeSubst` s
             in case t of
                    Nothing -> return (apply s'' xtype, s'', Just t')
                    Just t'' -> do
                        sF <- mgu (apply s'' t'') (apply s'' t')
                        return (apply (sF `composeSubst` s'') xtype, sF `composeSubst` s'', Just $ apply (sF `composeSubst` s'') t'')
     in case Map.lookup x env' of
            Nothing -> throwError $ "unbound variable: " ++ show x
            Just sigma -> do
                t <- instantiate sigma
                foldM f (t, nullSubst, Nothing) cases >>= \(xtype, s, Just t) -> return (s, t)
ti env exp@(EBApp e1 e2) =
    do
        tv <- newTyVar "a"
        (s1, t1) <- ti env e1
        (s2, t2) <- ti (apply s1 env) e2
        s3 <- mgu (apply s2 t1) (TFunc t2 tv)
        return (s3 `composeSubst` s2 `composeSubst` s1, apply s3 tv)
        `catchError` \e -> throwError $ e ++ "\n in " ++ show exp
ti env (EBArith e1 e2 op) =
    do
        (s1, t1) <- ti env e1
        (s2, t2) <- ti (apply s1 env) e2
        s3 <- haveItBeInt (apply (s2 `composeSubst` s1) t1)
        s4 <- haveItBeInt (apply (s3 `composeSubst` s2 `composeSubst` s1) t2)
        return (s4 `composeSubst` s3 `composeSubst` s2 `composeSubst` s1, TInt)

typeInference :: Map.Map Idt Scheme -> ExpBound -> TI Type
typeInference env e = do
    (s, t) <- ti (TypeEnv env) e
    return (apply s t)

recurrentInference :: Map.Map Idt Scheme -> ExpBound -> Idt -> TI Type
recurrentInference env e name@(Idt name') = do
    tv <- newTyVar name'
    (s, t) <- ti (TypeEnv (Map.insert name (Scheme [] tv) env)) e
    s' <- mgu (apply s t) (apply s tv)
    return (apply (s' `composeSubst` s) t)

overloadInference :: Map.Map Idt Scheme -> VariantEnv -> ExpBound -> Idt -> Except String (Type, ExpBound)
overloadInference env venv (EBOverload xs) name =
    let unpair [] = ([], [])
        unpair ((h1, h2) : t) = let (t1, t2) = unpair t in (h1 : t1, h2 : t2)
        k =
            [ (t, x)
              | (Right t, x) <-
                    map
                        (\x -> let (res, _) = runTI venv (recurrentInference env x name) in (res, x))
                        xs
            ]
     in case unpair k of
            ([], []) -> throwError "no typeable overload"
            (types, xs) -> return (TOverload types, EBOverload xs)
overloadInference env venv e name =
    let (res, _) = runTI venv (recurrentInference env e name)
     in case res of
            Left err -> throwError err
            Right t -> return (t, e)

overloadify :: (Type, ExpBound) -> (Type, ExpBound)
overloadify (TOverload ts, EBOverload xs) = (TOverload ts, EBOverload xs)
overloadify (t, e) = (TOverload [t], EBOverload [e])

sumTypes :: Type -> Type -> Type
sumTypes (TOverload ts) (TOverload ts') = TOverload (ts ++ ts')
sumTypes (TOverload ts) t = TOverload (ts ++ [t])
sumTypes t (TOverload ts) = TOverload (t : ts)
sumTypes t t' = TOverload [t, t']