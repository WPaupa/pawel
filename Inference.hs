module Inference where

import AbsPawel
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set
import MatchChecker

-- Kod zaadaptowany z linka z moodla.
-- Format został nieco dostosowany do mojego,
-- ale styl jest mieszanką obydwu.
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
generalize env t = Scheme vars t where
    vars = Set.toList ((ftv t) `Set.difference` (ftv env))

unfunify :: Type -> Type
unfunify (TFunc t1 t2) = unfunify t2
unfunify t = t

-- W linku z moodla środowisko w Readerze jest puste,
-- ja wykorzystuję tę okazję do trzymania środowiska typów wariantowych
-- (przypisania typowe nadal przekazuję w argumencie, jak tam).
data TIState = TIState {tiSupply :: Int}
type TI a = ExceptT String (ReaderT VariantEnv (State TIState)) a
runTI :: VariantEnv -> TI a -> (Either String a, TIState)
runTI env t = runState (runReaderT (runExceptT t) env) $ TIState{tiSupply = 0}

newTyVar :: String -> TI Type
newTyVar prefix = do
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
    return (s2 `composeSubst` s1)
mgu (TVar u) t = varBind u t
mgu t (TVar u) = varBind u t
-- Inty unifikują się z funkcjami, ale nadal
-- są monomorficzne, czyli typ nigdy nie zunifikuje
-- się z większym od niego typem.
mgu TInt TInt = return nullSubst
-- Zgodny z deklaracją kod unifikacji inta z funkcją z inta jest taki:
-- mgu TInt (TFunc TInt b) = do
--     tv <- newTyVar "a"
--     mgu TInt (TFunc (TFunc tv tv) b)
-- Natomiast prowadzi on do natłoku przeładowań. Dla dobra programisty
-- nie unifikuje się bezpośrednio inta z funkcją z inta.
mgu TInt (TFunc TInt b) = throwError "TypeError: Int unified directly with function from Int"
mgu TInt (TFunc b TInt) = throwError "TypeError: Int unified directly with function to Int"
mgu TInt (TFunc (TFunc t1 t2) b) = do
    s1 <- mgu (TFunc t1 t2) b
    s2 <- mgu (apply s1 t1) (apply s1 t2)
    return (s2 `composeSubst` s1)
mgu TInt (TFunc (TVar a) b) = do
    tv <- newTyVar "a"
    s1 <- mgu (TVar a) b
    s2 <- mgu (apply s1 $ TVar a) (TFunc tv tv)
    return (s2 `composeSubst` s1)
mgu t1 TInt = mgu TInt t1
-- Dwa warianty się unifikują,
-- jeśli są tego samego typu wariantowego
-- i każdy argument konstruktora się unifikuje
mgu (TVariant name types) (TVariant name' types')
    | (length types == length types') && (name == name') =
        foldM
            ( \s (t1, t2) -> do
                s1 <- mgu t1 t2
                return (s1 `composeSubst` s)
            )
            nullSubst
            (zip types types')
    | otherwise =
        throwError $
            "TypeError, variant types "
                ++ show name ++ "(" ++ (show $ length types) ++ ") and "
                ++ show name' ++ "(" ++ (show $ length types') ++ ") do not match"
-- To też w sumie jest niezgodność z deklaracją trochę dla dobra programisty,
-- żeby nie tworzyło się za dużo przeładowań.
mgu (TVariant name types) (TFunc t1 t2) = throwError "TypeError: variant application not yet implemented"
mgu t1 t2 = throwError $ "types do not unify: " ++ show t1 ++ " vs. " ++ show t2

-- Inty możemy unifikować z funkcjami, więc potrzebujemy
-- dodatkowej funkcji na stwierdzenie, że coś np. może być pod ifem
-- Wtedy nie tylko musi się unifikować z intem, ale po prostu być intem. 
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

-- Główna funkcja do inferencji, zaadaptowana z moodla.
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
-- Żeby zinferować typ wariantowy, musimy zinferować typy wszystkich argumentów
-- oraz znaleźć konstruktor w środowisku i sprawdzić, czy faktycznie
-- konstruuje nasz typ.
ti env@(TypeEnv env') exp@(EBVariant name es) =
    let f (s, ts) e = do
            (s', t') <- ti (apply s env) e
            return (s' `composeSubst` s, (t' : ts))
     in case Map.lookup name env' of
            Nothing -> throwError $ "unbound variant constructor: " ++ show name
            Just sigma -> do
                t <- instantiate sigma
                case unfunify t of
                    TVariant name' ts' -> do
                        (s, ts) <- foldM f (nullSubst, []) es
                        s' <- mgu (TVariant name ts) (unfunify t)
                        return (s' `composeSubst` s, apply s' (unfunify t))
                    _ -> throwError $ "expected variant constructor, got " ++ show (unfunify t)
    `catchError` \e -> throwError $ e ++ "\n in " ++ show exp
ti env exp@(EBIf e1 e2 e3) = do
    (s1, t1) <- ti env e1
    s2 <- haveItBeInt (apply s1 t1)
    (s3, t2) <- ti (apply (s2 `composeSubst` s1) env) e2
    (s4, t3) <- ti (apply (s3 `composeSubst` s2 `composeSubst` s1) env) e3
    s5 <- mgu
        (apply (s4 `composeSubst` s3 `composeSubst` s2 `composeSubst` s1) t2)
        (apply (s4 `composeSubst` s3 `composeSubst` s2 `composeSubst` s1) t3)
    return (s5 `composeSubst` s4 `composeSubst` s3 `composeSubst` s2 `composeSubst` s1, apply s5 t3)
    `catchError` \e -> throwError $ e ++ "\n in " ++ show exp
-- Musimy najpierw uzgodnić typy argumentów
-- z tymi zadeklarowanymi, potem zinferować typ
-- wyrażenia pod letem w rozszerzonym o nie środowisku
-- i na koniec zinferować typ wyrażenia pod inem.
-- Poza tym let może być rekurencyjny, więc najpierw
-- wstawiamy jakąś zmienną typową do środwiska pod
-- nazwą letowaną, a potem unifikujemy to z otrzymanym typem.
-- Decyzja projektowa: nie bąbelkujemy errorów na zewnątrz leta, bo tworzy to chaos.
ti env@(TypeEnv env') exp@(EBLet x tds e1 e2) = do
    tv <- newTyVar "a"
    (s0, t0) <- ti (TypeEnv (Map.insert x (Scheme [] tv) env')) (EBLam Map.empty (map untype tds) e1)
    s0' <- mgu (apply s0 t0) (apply s0 tv)
    let t1 = apply s1 t0 
        s1 = s0' `composeSubst` s0
        typeof [] = newTyVar "a"
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
ti env exp@(EBLam lenv (n : t) e) = do
    tv <- newTyVar "a"
    let TypeEnv env' = remove env n
        env'' = TypeEnv (env' `Map.union` (Map.singleton n (Scheme [] tv)))
    (s1, t1) <- ti env'' (EBLam lenv t e)
    return (s1, TFunc (apply s1 tv) t1)
    `catchError` \e -> throwError $ e ++ "\n in " ++ show exp
-- Podobnie jak przy calc, funkcję inferującą typ
-- dla matcha wydzieliłem, bo logika dla przeładowanych
-- i nieprzeładowanych zmiennych jest taka sama.
ti env@(TypeEnv env') exp@(EOMatch pos x cases) =
    case Map.lookup x env' of
        Nothing -> throwError $ "unbound variable: " ++ show x
        Just sigma -> do
            t <- instantiate sigma
            case t of
                TOverload ts -> inferMatch env cases (ts !! pos)
                _ -> throwError $ "expected overloaded type, got " ++ show t
    `catchError` \e -> throwError $ e ++ "\n in " ++ show exp
ti env@(TypeEnv env') exp@(EBMatch x cases) =
    case Map.lookup x env' of
        Nothing -> throwError $ "unbound variable: " ++ show x
        Just sigma -> do
            t <- instantiate sigma
            inferMatch env cases t
    `catchError` \e -> throwError $ e ++ "\n in " ++ show exp
ti env exp@(EBApp e1 e2) = do
    tv <- newTyVar "a"
    (s1, t1) <- ti env e1
    (s2, t2) <- ti (apply s1 env) e2
    s3 <- mgu (apply s2 t1) (TFunc t2 tv)
    return (s3 `composeSubst` s2 `composeSubst` s1, apply s3 tv)
    `catchError` \e -> throwError $ e ++ "\n in " ++ show exp
-- Znowu wymagamy, żeby pod wyrażeniem arytmetycznym był int.
-- Może to wyglądać na mocne wymaganie, w szczególności skoro możemy
-- wyliczać wartości funkcji, ale wymaganie unifikacji
-- z intem jest za słabe, bo nie każda funkcja unifikująca się z intem
-- ma wartość. 
ti env exp@(EBArith e1 e2 op) = do
    (s1, t1) <- ti env e1
    (s2, t2) <- ti (apply s1 env) e2
    s3 <- haveItBeInt (apply (s2 `composeSubst` s1) t1)
    s4 <- haveItBeInt (apply (s3 `composeSubst` s2 `composeSubst` s1) t2)
    return (s4 `composeSubst` s3 `composeSubst` s2 `composeSubst` s1, TInt)
    `catchError` \e -> throwError $ e ++ "\n in " ++ show exp

-- Przechodzimy po wszystkich case'ach i dla każdego
-- wywołujemy funkcję f, która inferuje typ dla case'a.
-- W tej funkcji najpierw sprawdzamy, co wynika z matcha,
-- a potem w rozszerzonym środowisku inferujemy typ wyrażenia
-- i unifikujemy go z dotychczasowym. Tę pierwszą część
-- wykonuje funkcja doMatch, która dla zmiennej po prostu
-- dodaje ją do środowiska, a dla konstruktora sprawdza,
-- czy jest on zadeklarowany w środowisku i unifikuje
-- jego typ z typem matcha.
inferMatch :: TypeEnv -> [MatchCaseBound] -> Type -> TI (Subst, Type)
inferMatch env@(TypeEnv env') cases t =
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
     in foldM f (t, nullSubst, Nothing) cases >>= \(xtype, s, Just t) -> return (s, t)

-- Standardowa funkcja do inferencji.
typeInference :: Map.Map Idt Scheme -> ExpBound -> TI Type
typeInference env e = do
    (s, t) <- ti (TypeEnv env) e
    return (apply s t)

-- Funkcja do inferencji dla rekurencyjnych deklaracji,
-- w praktyce nie jest zbyt potrzebna ze względu na postać deklaracji,
-- ale zostaje dla pełności.
recurrentInference :: Map.Map Idt Scheme -> ExpBound -> Idt -> TI Type
recurrentInference env e name@(Idt name') = do
    tv <- newTyVar name'
    (s, t) <- ti (TypeEnv (Map.insert name (Scheme [] tv) env)) e
    s' <- mgu (apply s t) (apply s tv)
    return (apply (s' `composeSubst` s) t)

-- Funkcja do inferencji dla typów przeładowanych lub nie.
-- Właściwa funkcja do inferencji zakłada brak przeładowania,
-- więc musimy osobno zinferować każdy typ i zwrócić listę typów.
-- Jeśli w niektórych overloadach są błędy typowe, to użytkownik zwykle nie chce
-- o nich wiedzieć, bo jest to o wiele za dużo informacji.
overloadInference :: Map.Map Idt Scheme -> VariantEnv -> ExpBound -> Idt -> Except String (Type, ExpBound)
overloadInference env venv (EBOverload xs) name =
    let unpair [] = ([], [])
        unpair ((h1, h2) : t) = let (t1, t2) = unpair t in (h1 : t1, h2 : t2)
        k = [(t, x) | (Right t, x) <- map
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