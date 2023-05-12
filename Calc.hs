module Calc where

import AbsPawel
import Binder
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Data.Map hiding (filter, foldl, map)
import qualified Data.Map as Map
import OpParser
import Prelude hiding (lookup)

monadicFold :: (Monad m) => (b -> a -> b) -> b -> [m a] -> m b
monadicFold f b [] = return b
monadicFold f b (h : t) = do
    h' <- h
    monadicFold f (f b h') t

churchify :: Integer -> ExpBound
churchify n =
    let church 0 f x = x
        church n f x = f (church (n - 1) f x)
     in
        EBLam empty [Idt "f", Idt "x"] (church n (\q -> EBApp (EBVar $ Idt "f") q) (EBVar $ Idt "x"))

flattenExp :: [ExpBound] -> ExpBound
flattenExp [] = EBOverload []
flattenExp ((EBOverload xs) : t) = case flattenExp t of
    EBOverload ys -> EBOverload $ xs ++ ys
    y -> EBOverload $ xs ++ [y]
flattenExp (x : t) = case flattenExp t of
    EBOverload ys -> EBOverload $ x : ys
    y -> EBOverload $ [x, y]

bubbleOverload :: [ExpBound] -> ReaderT BEnv (Except String) ExpBound
bubbleOverload xs = fmap flattenExp $ mapM calc xs

allPairs :: [a] -> [b] -> [(a, b)]
allPairs l m = [(x, y) | x <- l, y <- m]

envSubstitute :: BEnv -> BEnv -> BEnv
envSubstitute lenv nenv = Map.map
    ( \x -> case x of
        EBVar y -> case lookup y nenv of
            Nothing -> x
            Just z -> z
        _ -> x
    )
    lenv

tryIntify :: ExpBound -> ReaderT BEnv (Except String) (Maybe Integer)
tryIntify (EBInt x) = return $ Just x
tryIntify x = do
    x' <- calc $ EBApp (EBApp x (EBLam empty [Idt "x"] $ EBArith (EBVar $ Idt "x") (EBInt 1) (ariOp (+)))) (EBInt 0)
    case x' of
        EBInt x'' -> return $ Just x''
        _ -> return Nothing

calc :: ExpBound -> ReaderT BEnv (Except String) ExpBound
calc (EBVar x) = do
    env <- ask
    case lookup x env of
        Nothing -> return $ EBVar x
        Just x -> calc x
calc (EBInt x) = return $ EBInt x
calc (EBIf e1 e2 e3) = do
    e1' <- calc e1
    case e1' of
        EBInt 0 -> calc e3
        EBInt _ -> calc e2
        EBOverload xs -> bubbleOverload $ map (\x -> EBIf x e2 e3) xs
        _ -> return $ EBIf e1' e2 e3
calc (EBLet x t e1 e2) = do
    env <- ask
    local (insert x $ EBLam (insert x (EBVar x) env) (map untype t) e1) (calc e2) -- jeśli mam dostęp, to łatwo
calc (EBLam env [] e) = local (envSubstitute env) $ calc e
calc (EBLam env x e) = do
    env' <- ask
    return $ EBLam (envSubstitute env env') x e
calc (EBApp e1 e2) = do
    e1' <- calc e1
    e2' <- calc e2
    case e1' of
        EBInt x -> if x < 0 then throwError "Applying negative integer" else calc $ EBApp (churchify x) e2'
        EBOverload xs -> bubbleOverload $ map (\x -> EBApp x e2') xs
        EBLam env [] e -> local (envSubstitute env) $ calc (EBApp e e2')
        EBLam env (h : t) e -> local (\env' -> insert h e2' $ envSubstitute env env') $ calc (EBLam (insert h e2' env) t e)
        EBVariant name vs -> calc $ EBVariant name $ map (\v -> EBApp v e2') vs
        _ -> return $ EBApp e1' e2'
calc (EBOverload xs) = mapM calc xs >>= return . flattenExp
calc (EBVariant x xs) = mapM calc xs >>= return . EBVariant x
calc (EOMatch n x []) = throwError "Match error"
calc (EOMatch n x (CaseBound m e : t)) = do
    env <- ask
    case lookup x env of
        Nothing -> return $ EOMatch n x (CaseBound m e : t)
        Just (EBOverload xs) -> do
            xv <- calc (xs !! n)
            calcMatch m e x t xv
        Just x' -> do
            xv <- calc x'
            calcMatch m e x t xv
calc (EBMatch x []) = throwError "Match error"
calc (EBMatch x (CaseBound m e : t)) = do
    env <- ask
    case lookup x env of
        Just x' -> do
            xv <- calc x'
            calcMatch m e x t xv
        Nothing -> return $ EBMatch x (CaseBound m e : t)
calc (EBArith x y (AriOp f)) = do
    x' <- calc x
    y' <- calc y
    x'' <- tryIntify x'
    y'' <- tryIntify y'
    case (x', y') of
        (EBInt x'', EBInt y'') -> calcF f x'' y''
        (EBOverload xs, EBInt y'') ->
            fmap flattenExp $
                mapM (\x'' -> calc $ EBArith x'' (EBInt y'') (AriOp f)) xs
        (EBInt x'', EBOverload ys) ->
            fmap flattenExp $
                mapM (\y'' -> calc $ EBArith (EBInt x'') y'' (AriOp f)) ys
        (EBOverload xs, EBOverload ys) ->
            fmap flattenExp $
                mapM (\(x'', y'') -> calc $ EBArith x'' y'' (AriOp f)) $
                    allPairs xs ys
        (nl, EBInt nr) -> case x'' of
            Just nl' -> calcF f nl' nr
            Nothing -> return $ EBArith nl (EBInt nr) (AriOp f)
        (EBInt nl, nr) -> case y'' of
            Just nr' -> calcF f nl nr'
            Nothing -> return $ EBArith (EBInt nl) nr (AriOp f)
        (nl, nr) -> case (x'', y'') of
            (Just nl', Just nr') -> calcF f nl' nr'
            _ -> return $ EBArith nl nr (AriOp f)
  where
    calcF :: (Integer -> Integer -> Maybe Integer) -> Integer -> Integer -> ReaderT BEnv (Except String) ExpBound
    calcF f x y = case f x y of
        Just x -> return $ EBInt x
        Nothing -> throwError "Arithmetic error"
calc (EOVar pos x) = do
    env <- ask
    case lookup x env of
        Nothing -> return $ EOVar pos x
        Just (EBOverload xs) -> calc $ xs !! pos
        Just x -> return x

calcMatch :: Match -> ExpBound -> Idt -> [MatchCaseBound] -> ExpBound -> ReaderT BEnv (Except String) ExpBound
calcMatch m e x t x' =
    case x' of
        EBVariant y ys -> case match y m ys of
            Nothing -> calc $ EBMatch x t
            Just kvs -> local (inserts kvs) (calc e)
        EBOverload xs -> fmap flattenExp $ mapM (calcMatch m e x t) xs
        x'' -> case m of
            MVar y -> local (insert y x'') (calc e)
            _ -> return $ EBMatch x (CaseBound m e : t)

match :: Idt -> Match -> [ExpBound] -> Maybe [(Idt, ExpBound)]
match q (MVar x) l = Just [(x, EBVariant q l)]
match q (MCons x xs) ys
    | (length xs == length ys) && (q == x) = monadicFold (\a b -> a ++ b) [] $ zipWith match' xs ys
    | otherwise = Nothing

match' :: Match -> ExpBound -> Maybe [(Idt, ExpBound)]
match' (MVar x) y = Just [(x, y)]
match' (MCons x xs) (EBVariant y ys) = if x == y then match y (MCons x xs) ys else Nothing
match' _ _ = Nothing

