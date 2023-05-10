module Binder where

import Control.Monad.Reader
import Control.Monad
import Prelude hiding (lookup)
import Data.Map hiding (map, foldl, filter)
import OpParser
import AbsPawel
import Preprocessor

inserts :: Ord a => [(a, b)] -> Map a b -> Map a b
inserts kvs m = foldl (\m (k, v) -> insert k v m) m kvs

bubble' :: [Reader BEnv ExpBound] -> Reader BEnv [ExpBound]
bubble' [] = return []
bubble' (h:t) = do
    h' <- h
    t' <- bubble' t
    case h' of
        EBOverload es -> return $ es ++ t'
        _ -> return $ h' : t'

bubble :: [Reader BEnv ExpBound] -> Reader BEnv ExpBound
bubble hs = do
    hs' <- bubble' hs
    case hs' of
        [] -> return $ EBOverload []
        [h] -> return h
        _ -> return $ EBOverload hs'

bind :: Exp -> Reader BEnv ExpBound

bind (EVar x) = do
    env <- ask
    case lookup x env of
        Just (EBOverload xs) -> return $ EBOverload $ map (\y -> EOVar y x) [0..(length xs - 1)]
        _ -> return $ EBVar x
bind (EInt x) = return $ EBInt x
bind (ELet x tds e1 e2) = let bind2 e1' = do {
    e2' <- (local (insert x e1') $ bind e2);
    case e2' of
        EBOverload es -> return $ EBOverload $ map (\e -> EBLet x tds e1' e) es
        _ -> return $ EBLet x tds e1' e2';
    } in do
        e1' <- local (inserts $ map (\x -> (untype x, EBVar $ untype x)) tds) $ bind e1
        case e1' of
            EBOverload es -> bubble $ map (\e -> bind2 e) es
            _ -> bind2 e1'
bind (EIf e1 e2 e3) = let 
    bind3 e1' e2' = do {
        e3' <- bind e3;
        case e3' of
            EBOverload es -> return $ EBOverload $ map (\e -> EBIf e1' e2' e) es
            _ -> return $ EBIf e1' e2' e3';
        }
    bind2 e1' = do {
        e2' <- bind e2;
        case e2' of
            EBOverload es -> bubble $ map (\e -> bind3 e1' e) es
            _ -> bind3 e1' e2';
        } in do {
        e1' <- bind e1;
        case e1' of
            EBOverload es -> bubble $ map (\e -> bind2 e) es
            _ -> bind2 e1';
        }
bind (EApp e1 e2) = let
    bind2 e1' = do {
        e2' <- bind e2;
        case e2' of
            EBOverload es -> return $ EBOverload $ map (\e -> EBApp e1' e) es
            _ -> return $ EBApp e1' e2';
        } in do {
        e1' <- bind e1;
        case e1' of
            EBOverload es -> bubble $ map (\e -> bind2 e) es
            _ -> bind2 e1';
        }
bind (ELam xs e) = do
    env <- ask
    e' <- local (inserts $ map (\x -> (x, EBVar x)) xs) $ bind e
    case e' of
        EBOverload es -> return $ EBOverload $ map (\e -> EBLam env xs e) es
        _ -> return $ EBLam env xs e'
bind (EMatch x mcs) = let
    bindMatch (MVar x) = insert x (EBVar x)
    bindMatch (MCons x []) = id
    bindMatch (MCons x (h:t)) = bindMatch h . bindMatch (MCons x t) 
    bindMC (Case p e) = do
        e' <- local (bindMatch p) $ bind e
        case e' of
            EBOverload es -> return $ CaseBoundOverload $ map (\e -> CaseBound p e) es
            _ -> return $ CaseBound p e'
    bindMCs [] = return $ EBMatch x []
    bindMCs (h:t) = do
        h' <- bindMC h
        t' <- bindMCs t
        case (h', t') of 
            (CaseBound m e, EBMatch x' ts) -> return $ EBMatch x' $ (CaseBound m e) : ts
            (CaseBoundOverload hs, EBMatch x' ts) -> bubble $ map (\c -> return $ EBMatch x' $ c : ts) hs
            (CaseBound m e, EBOverload ts) -> bubble $ map (\(EBMatch x' ms) -> return $ EBMatch x' $ (CaseBound m e) : ms) ts
            (CaseBoundOverload hs, EBOverload ts) -> bubble $ map (\(EBMatch x' ms) -> bubble $ map (\c -> return $ EBMatch x' $ c : ms) hs) ts
    in bindMCs mcs

makeOverloadsRecurrent :: Idt -> ExpBound -> ExpBound
makeOverloadsRecurrent name (EBOverload xs) =
    let recOver n (EBVar name') = if name == name' then EOVar n name else EBVar name'
        recOver n (EBVariant name' xs) = EBVariant name' $ map (recOver n) xs
        recOver n (EBIf e1 e2 e3) = EBIf (recOver n e1) (recOver n e2) (recOver n e3)
        recOver n (EBLet name tds e1 e2) = 
            if elem name (map untype tds) 
                then 
                    EBLet name tds e1 (recOver n e2) 
                else 
                    EBLet name tds (recOver n e1) (recOver n e2)
        recOver n (EBLam env xs e) = if elem name xs then EBLam env xs e else EBLam env xs (recOver n e)
        recOver n (EBMatch x cases) = 
            let inAny name (MVar name') = name == name'
                inAny name (MCons consn xs) = any (inAny name) xs
                help [] = []
                help ((CaseBound p e):xs) = if inAny name p then (CaseBound p e):(help xs) else (CaseBound p (recOver n e)):(help xs) in
            EBMatch x $ help cases
        recOver n (EBApp e1 e2) = EBApp (recOver n e1) (recOver n e2)
        recOver n (EBArith e1 e2 op) = EBArith (recOver n e1) (recOver n e2) op 
        recOver n x = x in
    EBOverload $ map (\(x, n) -> recOver n x) (zip xs [0..])
makeOverloadsRecurrent name x = x

bindRecurrent :: Exp -> Idt -> BEnv -> ExpBound
bindRecurrent x fname env = makeOverloadsRecurrent fname $ runReader (bind x) (insert fname (EBVar fname) env)