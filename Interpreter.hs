module Interpreter where

import Control.Monad.Reader
import Prelude hiding (lookup)
import Data.Map hiding (map, foldl, filter)
import OpParser
import AbsPawel
import Preprocessor

type Env = (Map Idt Lam, Map Idt (Idt, Integer, Integer), Map Idt ([Idt], [Variant]))
chenv :: (Map Idt Lam -> Map Idt Lam) -> Reader Env a -> Reader Env a
chenv x = local (\(a, b, c) -> (x a, b, c))
ins :: Idt -> Lam -> Env -> Env
ins x f (a, b, c) = (insert x f a, b, c)

data Lam = LInt Integer | LApp (Lam -> Lam) | LVariant Idt [Lam] | LOverloads [(Type, Lam)]

instance Show Lam where
    show (LInt x) = show x
    show (LApp _) = "function"
    show (LVariant name args) = (show name) ++ " " ++ show args
    show (LOverloads _) = "overloaded"

evalExp :: Exp -> Reader Env Lam

evalExp (EUnparsed es) = evalExp $ infixate $ EUnparsed es
evalExp (EVar x) = do
    (env, _, _) <- ask
    case lookup x env of
        Just e -> return e
        Nothing -> error $ "variable " ++ (show x) ++ " not found"
evalExp (EInt x) = return $ LInt x
evalExp (ELet x tds e1 e2) = do
    e1' <- evalExp e1
    chenv (insert x e1') $ evalExp e2
evalExp (EIf e1 e2 e3) = do
    e1' <- evalExp e1
    case e1' of
        LInt 0 -> evalExp e3
        LInt _ -> evalExp e2
        _ -> error "ifte not overloaded"
evalExp (ELam [] e) = evalExp e
evalExp (ELam (x:xs) e) = do
    env <- ask
    return $ LApp $ \x' -> runReader (evalExp $ ELam xs e) (ins x x' env)
evalExp (EMatch x []) = error "match not found"
evalExp (EMatch x (Case m e:ms)) = do
    x' <- evalExp $ EVar x
    case match m x' of
        Just change -> chenv change $ evalExp e
        Nothing -> evalExp $ EMatch x ms

evalExp (EApp e1 e2) = do
    e1' <- evalExp e1
    e2' <- evalExp e2
    case e1' of
        LApp f -> return $ f e2'
        LOverloads os -> return $ evalOverloads os e2'
        LVariant name args -> return $ LVariant name (args ++ [e2'])
        LInt m -> return $ LInt $ m + 1

evalOverloads :: [(Type, Lam)] -> Lam -> Lam
evalOverloads [] _ = error "overloaded function not found"
evalOverloads ((type, f):os) arg = case f of
    LApp g -> g arg
    LOverloads fs -> evalOverloads fs arg
    LVariant name args -> LVariant name (args ++ [arg])
    LInt m -> LInt $ m + 1

match :: Match -> Lam -> Maybe (Map Idt Lam -> Map Idt Lam)
match _ (LApp _) = Nothing
match _ (LOverloads _) = Nothing
match (MVar x) y = Just $ insert x y
match (MCons x xs) (LVariant y ys) 
    | x == y && length xs == length ys = foldl (\change (x, y) -> do
        env <- change
        newchange <- match x y
        return $ newchange . env
    ) (Just id) (zip xs ys)
    | otherwise = Nothing
match _ _ = Nothing
