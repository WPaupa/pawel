module Calc where

import Control.Monad.Reader
import Control.Monad
import Prelude hiding (lookup)
import Data.Map hiding (map, foldl, filter)
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
    EBLam [Idt "f", Idt "x"] (church n (\q -> EBApp (EBVar $ Idt "f") q) (EBVar $ Idt "x"))

substitute :: ExpBound -> Reader BEnv ExpBound
substitute (EBVar x) = do
    env <- ask
    case lookup x env of
        Nothing -> return $ EBVar x
        Just x -> return x
substitute (EOVar pos x) = do
    env <- ask
    case lookup x env of
        Nothing -> return $ EOVar pos x
        Just (EBOverload xs) -> return $ xs !! pos
        Just x -> return x
substitute (EBInt x) = return $ EBInt x
substitute (EBIf e1 e2 e3) = do
    e1' <- substitute e1
    e2' <- substitute e2
    e3' <- substitute e3
    return $ EBIf e1' e2' e3'
substitute (EBLet x t e1 e2) = do
    e1' <- local (inserts $ map (\x -> (untype x, EBVar $ untype x)) t) $ substitute e1
    e2' <- local (insert x e1') (substitute e2)
    return $ EBLet x t e1' e2'
substitute (EBLam [] e) = do
    e' <- substitute e
    return e'
substitute (EBLam xs e) = do
    e' <- local (inserts $ map (\x -> (x, EBVar x)) xs) $ substitute e
    return $ EBLam xs e'
substitute (EBMatch x cs) = do
    cs' <- mapM (\(CaseBound m e) -> do
        e' <- substitute e
        return $ CaseBound m e') cs
    return $ EBMatch x cs'
substitute (EBApp e1 e2) = do
    e1' <- substitute e1
    e2' <- substitute e2
    return $ EBApp e1' e2'
substitute (EBOverload xs) = do
    xs' <- mapM substitute xs
    return $ EBOverload xs'
substitute (EBArith x y op) = do
    x' <- substitute x
    y' <- substitute y
    return $ EBArith x' y' op
substitute (EBVariant name ts) = do
    ts' <- mapM substitute ts
    return $ EBVariant name ts'
substitute (EBCons f) = return $ EBCons f

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
calc (EBLet x t e1 e2) = local (insert x $ EBLam (map untype t) e1) (calc e2)
calc (EBLam [] e) = calc e
calc (EBLam x e) = return $ Right $ EBLam x e
calc (EBApp e1 e2) = do
    e1' <- calc e1
    e2' <- calc e2
    case e1' of
        Left x -> calc $ EBApp (churchify x) (coerce e2')
        Right (EBOverload xs) -> bubbleOverload $ map (\x -> EBApp x (coerce e2')) xs
        Right (EBLam [] e) -> calc (EBApp e (coerce e2'))
        Right (EBLam (h:t) e) -> local (insert h $ coerce e2') $ calc $ runReader (substitute $ EBLam t e) $ fromList [(h, coerce e2')]
        Right (EBVariant name vs) -> calc $ EBVariant name $ map (\v -> EBApp v (coerce e2')) vs
        Right (EBCons (FWCons f)) -> calc $ f (coerce e2')
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
calc (EBArith x y (AriOp f)) = do
    x' <- calc x
    y' <- calc y
    case (x', y') of
        (Left x'', Left y'') -> return $ Left $ f x'' y''
        (Right (EBOverload xs), Left y'') -> fmap (uncoerce . flattenExp) $ 
            mapM (\x'' -> fmap coerce (calc $ EBArith x'' (EBInt y'') (AriOp f))) xs
        (Left x'', Right (EBOverload ys)) -> fmap (uncoerce . flattenExp) $ 
            mapM (\y'' -> fmap coerce (calc $ EBArith (EBInt x'') y'' (AriOp f))) ys
        (Right (EBOverload xs), Right (EBOverload ys)) -> fmap (uncoerce . flattenExp) $
            mapM (\(x'', y'') -> fmap coerce (calc $ EBArith x'' y'' (AriOp f))) $ allPairs xs ys
        _ -> return $ Right $ EBArith x y (AriOp f)
calc (EOVar pos x) = do
    env <- ask
    case lookup x env of
        Nothing -> return $ Right $ EOVar pos x
        Just (EBOverload xs) -> calc $ xs !! pos
        Just x -> return $ Right x
calc (EBCons f) = return $ Right $ EBCons f

match :: Idt -> Match -> [ExpBound] -> Maybe [(Idt, ExpBound)]
match q (MVar x) l = Just [(x, EBVariant q l)]
match q (MCons x xs) ys 
    | length xs == length ys = monadicFold (\a b -> a ++ b) [] $ zipWith match' xs ys
    | otherwise = Nothing

match' :: Match -> ExpBound -> Maybe [(Idt, ExpBound)]
match' (MVar x) y = Just [(x, y)]
match' (MCons x xs) (EBVariant y ys) = if x == y then match y (MCons x xs) ys else Nothing
match' _ _ = Nothing

aenv = inserts [(Idt "{-}", EBLam [Idt "x", Idt "y"] $ EBArith (EBVar $ Idt "x") (EBVar $ Idt "y") $ AriOp (-)), 
                (Idt "{*}", EBLam [Idt "x", Idt "y"] $ EBArith (EBVar $ Idt "x") (EBVar $ Idt "y") $ AriOp (*)),
                (Idt "{+}", EBLam [Idt "x", Idt "y"] $ EBArith (EBVar $ Idt "x") (EBVar $ Idt "y") $ AriOp (+)), 
                (Idt "{/}", EBLam [Idt "x", Idt "y"] $ EBArith (EBVar $ Idt "x") (EBVar $ Idt "y") $ AriOp (\x y -> x `div` y)),
                (Idt "{>}", EBLam [Idt "x", Idt "y"] $ EBArith (EBVar $ Idt "x") (EBVar $ Idt "y") $ AriOp (\x y -> if x > y then 1 else 0)),
                (Idt "{<}", EBLam [Idt "x", Idt "y"] $ EBArith (EBVar $ Idt "x") (EBVar $ Idt "y") $ AriOp (\x y -> if x < y then 1 else 0)),
                (Idt "{>=}", EBLam [Idt "x", Idt "y"] $ EBArith (EBVar $ Idt "x") (EBVar $ Idt "y") $ AriOp (\x y -> if x >= y then 1 else 0)),
                (Idt "{<=}", EBLam [Idt "x", Idt "y"] $ EBArith (EBVar $ Idt "x") (EBVar $ Idt "y") $ AriOp (\x y -> if x <= y then 1 else 0)),
                (Idt "{==}", EBLam [Idt "x", Idt "y"] $ EBArith (EBVar $ Idt "x") (EBVar $ Idt "y") $ AriOp (\x y -> if x == y then 1 else 0))] empty

cc x = runReader (calc x) aenv

bb x fname = runReader (bind x) (insert (Idt fname) (EBVar $ Idt fname) aenv)
bba x fname aenv = runReader (bind x) (insert (Idt fname) (EBVar $ Idt fname) aenv)

x = EVar $ Idt "x"
xm1 = EApp (EApp (EVar $ Idt "{-}") x) (EInt 1) 
fact = ELam [Idt "x"] $ EIf x (EApp (EApp (EVar $ Idt "{*}") x) (EApp (EVar $ Idt "fact") xm1)) (EInt 1)

extend x fname env = insert (Idt fname) (bba x fname env) env
doe y x fname env = runReader (calc (bb y "abc'")) (extend x fname env)

fact5 = doe (EApp fact $ EInt 5) fact "fact" aenv