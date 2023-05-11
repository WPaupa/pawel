module Calc where

import Control.Monad.Reader
import Control.Monad
import Prelude hiding (lookup)
import Data.Map hiding (map, foldl, filter)
import qualified Data.Map as Map
import OpParser
import AbsPawel
import Preprocessor
import Binder

monadicFold :: Monad m => (b -> a -> b) -> b -> [m a] -> m b
monadicFold f b [] = return b
monadicFold f b (h:t) = do
    h' <- h
    monadicFold f (f b h') t 

coerce :: Either Integer ExpBound -> ExpBound
coerce (Left x) = EBInt x
coerce (Right x) = x

churchify :: Integer -> ExpBound
churchify n = let
    church 0 f x = x
    church n f x = f (church (n-1) f x) in
    EBLam empty [Idt "f", Idt "x"] (church n (\q -> EBApp (EBVar $ Idt "f") q) (EBVar $ Idt "x"))

flattenExp :: [ExpBound] -> ExpBound
flattenExp [x] = x
flattenExp ((EBOverload xs):t) = case flattenExp t of
    EBOverload ys -> EBOverload $ xs ++ ys
    y -> EBOverload $ xs ++ [y]
flattenExp (x:t) = case flattenExp t of
    EBOverload ys -> EBOverload $ x:ys
    y -> EBOverload $ [x, y]

uncoerce :: ExpBound -> Either Integer ExpBound
uncoerce (EBInt x) = Left x
uncoerce x = Right x

bubbleOverload :: [ExpBound] -> Reader BEnv (Either Integer ExpBound)
bubbleOverload xs = fmap (uncoerce . flattenExp) $ mapM ((fmap coerce) . calc) xs

allPairs :: [a] -> [b] -> [(a,b)]
allPairs l m = [(x, y) | x <- l, y <- m]

envSubstitute :: BEnv -> BEnv -> BEnv
envSubstitute lenv nenv = Map.map (\x -> case x of
    EBVar y -> case lookup y nenv of
        Nothing -> x
        Just z -> z
    _ -> x) lenv

tryIntify :: (Either Integer ExpBound) -> Reader BEnv (Maybe Integer)
tryIntify (Left x) = return $ Just x
tryIntify (Right x) = do
    x' <- calc $ EBApp (EBApp x (EBLam empty [Idt "x"] $ EBArith (EBVar $ Idt "x") (EBInt 1) (AriOp (+)))) (EBInt 0)
    case x' of
        Left x'' -> return $ Just x''
        _ -> return Nothing

calc :: ExpBound -> Reader BEnv (Either Integer ExpBound)
calc (EBVar x) = do
    env <- ask
    case lookup x env of
        Nothing -> return $ Right $ EBVar x
        Just (EBInt x) -> return $ Left x
        Just x -> calc x
calc (EBInt x) = return $ Left x
calc (EBIf e1 e2 e3) = do
    e1' <- calc e1
    case e1' of
        Left 0 -> calc e3
        Left _ -> calc e2
        Right (EBOverload xs) -> bubbleOverload $ map (\x -> EBIf x e2 e3) xs
        Right e1'' -> return $ Right $ EBIf e1'' e2 e3
calc (EBLet x t e1 e2) = do
    env <- ask
    local (insert x $ EBLam env (map untype t) e1) (calc e2)
calc (EBLam env [] e) = local (envSubstitute env) $ calc e
calc (EBLam env x e) = do
    env' <- ask
    return $ Right $ EBLam (envSubstitute env env') x e
calc (EBApp e1 e2) = do
    e1' <- calc e1
    e2' <- calc e2
    case e1' of
        Left x -> calc $ EBApp (churchify x) (coerce e2')
        Right (EBOverload xs) -> bubbleOverload $ map (\x -> EBApp x (coerce e2')) xs
        Right (EBLam env [] e) -> local (envSubstitute env) $ calc (EBApp e (coerce e2'))
        Right (EBLam env (h:t) e) -> local (\env' -> insert h (coerce e2') $ envSubstitute env env') $ calc (EBLam (insert h (coerce e2') env) t e)
        Right (EBVariant name vs) -> calc $ EBVariant name $ map (\v -> EBApp v (coerce e2')) vs
        Right e -> return $ Right $ EBApp e $ coerce e2'
calc (EBOverload [x]) = calc x
calc (EBOverload xs) = mapM calc xs >>= return . uncoerce . flattenExp . map coerce
calc (EBVariant x xs) = mapM calc xs >>= return . Right . EBVariant x . map coerce
calc (EBMatch x []) = error "Match error"
calc (EBMatch x (CaseBound m e:t)) = do
    env <- ask
    case lookup x env of
        Just x' -> do
            xv <- calc x'
            calcMatch (coerce xv)
        Nothing -> return $ Right $ EBMatch x (CaseBound m e:t)
    where 
        calcMatch x' =
            case x' of
                EBVariant y ys -> case match y m ys of
                    Nothing -> calc $ EBMatch x t
                    Just kvs -> local (inserts kvs) (calc e)
                EBOverload xs -> fmap (uncoerce . flattenExp) $ mapM ((fmap coerce) . calcMatch) xs
                x'' -> case m of
                    MVar y -> local (insert y x'') (calc e)
                    _ -> return $ Right $ EBMatch x (CaseBound m e:t)
calc (EBArith x y (AriOp f)) = do -- ogarnąć kwestię intów
    x' <- calc x
    y' <- calc y
    x'' <- tryIntify x'
    y'' <- tryIntify y'
    case (x', y') of
        (Left x'', Left y'') -> return $ Left $ f x'' y''
        (Right (EBOverload xs), Left y'') -> fmap (uncoerce . flattenExp) $ 
            mapM (\x'' -> fmap coerce (calc $ EBArith x'' (EBInt y'') (AriOp f))) xs
        (Left x'', Right (EBOverload ys)) -> fmap (uncoerce . flattenExp) $ 
            mapM (\y'' -> fmap coerce (calc $ EBArith (EBInt x'') y'' (AriOp f))) ys
        (Right (EBOverload xs), Right (EBOverload ys)) -> fmap (uncoerce . flattenExp) $
            mapM (\(x'', y'') -> fmap coerce (calc $ EBArith x'' y'' (AriOp f))) $ allPairs xs ys
        (Right nl, Left nr) -> case x'' of
            Just nl' -> return $ Left $ f nl' nr
            Nothing -> return $ Right $ EBArith nl (EBInt nr) (AriOp f)
        (Left nl, Right nr) -> case y'' of
            Just nr' -> return $ Left $ f nl nr'
            Nothing -> return $ Right $ EBArith (EBInt nl) nr (AriOp f)
        (Right nl, Right nr) -> case (x'', y'') of
            (Just nl', Just nr') -> return $ Left $ f nl' nr'
            _ -> return $ Right $ EBArith nl nr (AriOp f)
calc (EOVar pos x) = do
    env <- ask
    case lookup x env of
        Nothing -> return $ Right $ EOVar pos x
        Just (EBOverload xs) -> calc $ xs !! pos
        Just x -> return $ Right x

match :: Idt -> Match -> [ExpBound] -> Maybe [(Idt, ExpBound)]
match q (MVar x) l = Just [(x, EBVariant q l)]
match q (MCons x xs) ys 
    | length xs == length ys = monadicFold (\a b -> a ++ b) [] $ zipWith match' xs ys
    | otherwise = Nothing

match' :: Match -> ExpBound -> Maybe [(Idt, ExpBound)]
match' (MVar x) y = Just [(x, y)]
match' (MCons x xs) (EBVariant y ys) = if x == y then match y (MCons x xs) ys else Nothing
match' _ _ = Nothing