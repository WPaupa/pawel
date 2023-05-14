module Binder where

import AbsPawel
import Control.Monad
import Control.Monad.Reader
import Data.Map hiding (filter, foldl, map)
import OpParser
import Prelude hiding (lookup)

inserts :: (Ord a) => [(a, b)] -> Map a b -> Map a b
inserts kvs m = foldl (\m (k, v) -> insert k v m) m kvs

-- Funkcja bubble bierze listę może przeciążonych
-- wyrażeń i zwraca przeciążone wyrażenie, które
-- jest ich sumą. Przy okazji wykonuje to wewnątrz monady.
bubble' :: [Reader BEnv ExpBound] -> Reader BEnv [ExpBound]
bubble' [] = return []
bubble' (h : t) = do
    h' <- h
    t' <- bubble' t
    case h' of
        EBOverload es -> return $ es ++ t'
        _ -> return $ h' : t'

-- Dla wygody programisty pojedyncze overloady są traktowane
-- jak wyrażenia nieprzeładowane. Na takie ułatwienie
-- możemy sobie jednak pozwolić tylko na tym poziomie,
-- żeby nie nadać przypadkiem przeładowanemu wyrażeniu
-- nieprzeładowanego typu i vice versa.
bubble :: [Reader BEnv ExpBound] -> Reader BEnv ExpBound
bubble hs = do
    hs' <- bubble' hs
    case hs' of
        [] -> return $ EBOverload []
        [h] -> return h
        _ -> return $ EBOverload hs'

-- Funkcja bind przeciąża wyrażenie w taki sposób,
-- żeby każde wystąpienie zmiennej przeładowanej miało przypisany
-- sobie numer przeładowania, do którego się odwołuje.
-- Robi to w ten sposób, żeby przeciążenie występowało tylko
-- na najwyższym poziomie, więc cały czas bąbelkuje przeładowania w górę.
bind :: Exp -> Reader BEnv ExpBound
bind (EVar x) = do
    env <- ask
    case lookup x env of
        Just (EBOverload xs) -> return $ EBOverload $ map (\y -> EOVar y x) [0 .. (length xs - 1)]
        _ -> return $ EBVar x
bind (EInt x) = return $ EBInt x
bind (ELet x tds e1 e2) =
    let bind2 e1' = do
            e2' <- (local (insert x e1') $ bind e2)
            case e2' of
                EBOverload es -> return $ EBOverload $ map (\e -> EBLet x tds e1' e) es
                _ -> return $ EBLet x tds e1' e2'
     in do
            e1' <- local (inserts $ map (\x -> (untype x, EBVar $ untype x)) tds) $ bind e1
            case e1' of
                EBOverload es -> bubble $ map (\e -> bind2 e) es
                _ -> bind2 e1'
bind (EIf e1 e2 e3) =
    let bind3 e1' e2' = do
            e3' <- bind e3
            case e3' of
                EBOverload es -> return $ EBOverload $ map (\e -> EBIf e1' e2' e) es
                _ -> return $ EBIf e1' e2' e3'
        bind2 e1' = do
            e2' <- bind e2
            case e2' of
                EBOverload es -> bubble $ map (\e -> bind3 e1' e) es
                _ -> bind3 e1' e2'
     in do
        e1' <- bind e1
        case e1' of
            EBOverload es -> bubble $ map (\e -> bind2 e) es
            _ -> bind2 e1'
bind (EApp e1 e2) =
    let bind2 e1' = do
            e2' <- bind e2
            case e2' of
                EBOverload es -> return $ EBOverload $ map (\e -> EBApp e1' e) es
                _ -> return $ EBApp e1' e2'
     in do
        e1' <- bind e1
        case e1' of
            EBOverload es -> bubble $ map (\e -> bind2 e) es
            _ -> bind2 e1'
bind (ELam xs e) = do
    env <- ask
    e' <- local (inserts $ map (\x -> (x, EBVar x)) xs) $ bind e
    case e' of
        EBOverload es -> return $ EBOverload $ map (\e -> EBLam env xs e) es
        _ -> return $ EBLam env xs e'
bind (EMatch x mcs) =
    -- Osobno musimy zbindować każdy match, i potem
    -- zbąbelkować wszystkie możliwe kombinacje.
    let bindMatch (MVar x) = insert x (EBVar x)
        bindMatch (MCons x []) = id
        bindMatch (MCons x (h : t)) = bindMatch h . bindMatch (MCons x t)
        bindMC (Case p e) = do
            e' <- local (bindMatch p) $ bind e
            case e' of
                EBOverload es -> return $ CaseBoundOverload $ map (\e -> CaseBound p e) es
                _ -> return $ CaseBound p e'
        fromMatch (EBMatch x ts) = ts
        fromMatch (EOMatch pos x ts) = ts
        bindMCs f [] = return $ f []
        bindMCs f (h : t) = do
            h' <- bindMC h
            t' <- bindMCs f t
            case (h', t') of
                (CaseBoundOverload hs, EBOverload ts) -> bubble $ map (\ms -> bubble $ map (\c -> return $ f $ c : (fromMatch ms)) hs) ts
                (CaseBound m e, EBOverload ts) -> bubble $ map (\ms -> return $ f $ (CaseBound m e) : (fromMatch ms)) ts
                (CaseBoundOverload hs, _) -> bubble $ map (\c -> return $ f $ c : (fromMatch t')) hs
                (CaseBound m e, _) -> return $ f $ (CaseBound m e) : (fromMatch t')
     in do
        env <- ask
        case lookup x env of
            -- Mamy dwa przypadki, dla przeciążonej i nieprzeciążonej zmiennej
            Just (EBOverload xs) -> bubble $ map (\y -> bindMCs (EOMatch y x) mcs) [0 .. (length xs - 1)]
            _ -> bindMCs (EBMatch x) mcs

-- Funkcja addOverloadNumber dodaje numer przeciążenia do zmiennej o danej nazwie.
-- Bierze pod uwagę to, że zmienne mogą być przysłaniane.
-- Poza tą subtelnością po prostu bąbelkuje.
addOverloadNumber :: Idt -> Int -> ExpBound -> ExpBound
addOverloadNumber name n (EBVar name') = if name == name' then EOVar n name else EBVar name'
addOverloadNumber name n (EBVariant name' xs) = EBVariant name' $ map (addOverloadNumber name n) xs
addOverloadNumber name n (EBIf e1 e2 e3) = EBIf (addOverloadNumber name n e1) (addOverloadNumber name n e2) (addOverloadNumber name n e3)
addOverloadNumber name n (EBLet x tds e1 e2) =
    if elem name (map untype tds)
        then EBLet x tds e1 (addOverloadNumber name n e2)
        else EBLet x tds (addOverloadNumber name n e1) (addOverloadNumber name n e2)
addOverloadNumber name n (EBLam env xs e) = if elem name xs then EBLam env xs e else EBLam env xs (addOverloadNumber name n e)
addOverloadNumber name n (EBMatch x cases) =
    let inAny name (MVar name') = name == name'
        inAny name (MCons consn xs) = any (inAny name) xs
        help [] = []
        help ((CaseBound p e) : xs) = if inAny name p then (CaseBound p e) : (help xs) else (CaseBound p (addOverloadNumber name n e)) : (help xs)
     in EBMatch x $ help cases
addOverloadNumber name n (EBApp e1 e2) = EBApp (addOverloadNumber name n e1) (addOverloadNumber name n e2)
addOverloadNumber name n (EBArith e1 e2 op) = EBArith (addOverloadNumber name n e1) (addOverloadNumber name n e2) op
addOverloadNumber name n x = x

-- Funkcja makeOverloadsRecurrent wiąże każde przeciążenie samo ze sobą.
-- Innymi słowy w każdym przeciążeniu zapewnia, że odwołanie rekurencyjne
-- będzie odwoływało się do tego samego przeciążenia.
makeOverloadsRecurrent :: Int -> Idt -> ExpBound -> ExpBound
makeOverloadsRecurrent startN name (EBOverload xs) =
    EBOverload $ map (\(x, n) -> addOverloadNumber name n x) (zip xs [startN ..])
makeOverloadsRecurrent startN name x = addOverloadNumber name startN x

-- Funkcja bindRecurrent wiąże identyfikatory, możliwe, że rekurencyjne.
-- Jest mocniejsza niż to, co potrzebujemy, bo nasze wyrażenia są zawsze postaci
-- let f = ... in f, więc nie muszą być na najwyższym poziomie rekurencyjnie.
-- Nie przeszkadza nam to jednak, zresztą przy obliczeniu i tak ten let spada
-- i wiązanie wchodzi w środowisko lambdy. Funkcja zostaje w tej formie dla ogólności.
bindRecurrent :: Exp -> Idt -> BEnv -> ExpBound
bindRecurrent x fname env = runReader (bind x) (insert fname (EBVar fname) env)