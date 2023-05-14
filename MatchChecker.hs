module MatchChecker where

import AbsPawel
import Control.Monad.Except
import Control.Monad.Reader
import Data.Map hiding (filter, foldl, map)
import Prelude hiding (lookup)

-- W tym pliku będzie sprawdzanie kompletności wzorców.
-- Jak na razie jest tutaj tylko reszta obsługi środowiska typów.

type VariantEnv = (Map Idt Scheme, Map Idt [Idt])
insertCons :: Idt -> Scheme -> VariantEnv -> VariantEnv
insertCons name t@(Scheme _ (TVariant tname _)) (a, b) = (insert name t a, insertWith (++) tname [name] b)

getConses :: Idt -> VariantEnv -> [Idt]
getConses name (_, b) = case lookup name b of
    Just x -> x
    Nothing -> []

emptyEnv :: VariantEnv
emptyEnv = (empty, empty)

-- Funkcja, która sprawdza, czy dana zmienna jest tak naprawdę
-- konstruktorem wariantu (w przeciwieństwie do Haskella i OCamla 
-- nie ma tutaj rozróżnienia składniowego), więc trzeba to robić
-- na bieżąco.
bindZeroargMatches :: Exp -> (VariantEnv, Map Idt Scheme) -> Except String Exp
bindZeroargMatches (EVar x) e = return $ EVar x
bindZeroargMatches (EInt x) e = return $ EInt x
bindZeroargMatches (ELet x tds e1 e2) e = do
    e1' <- bindZeroargMatches e1 e
    e2' <- bindZeroargMatches e2 e
    return $ ELet x tds e1' e2'
bindZeroargMatches (EIf e1 e2 e3) e = do
    e1' <- bindZeroargMatches e1 e
    e2' <- bindZeroargMatches e2 e
    e3' <- bindZeroargMatches e3 e
    return $ EIf e1' e2' e3'
bindZeroargMatches (ELam xs ex) e = fmap (ELam xs) (bindZeroargMatches ex e)
bindZeroargMatches (EMatch x cases) e@((ve, _), te) =
    let bindMatch :: Match -> Except String Match 
        bindMatch (MVar x) =
            if member x ve
                then case lookup x te of
                    Just (Scheme _ (TVariant _ _)) -> return $ MCons x []
                    _ -> return $ MVar x
                else return $ MVar x
        bindMatch (MCons name xs) =
            if member name ve
                then fmap (MCons name) (mapM bindMatch xs)
                else throwError $ "Unbound variant constructor: " ++ show name
     in fmap
            (EMatch x)
            ( mapM
                ( \(Case c ex) -> do
                    c' <- bindMatch c
                    ex' <- bindZeroargMatches ex e
                    return $ Case c' ex'
                )
                cases
            )
bindZeroargMatches (EApp e1 e2) e = do
    e1' <- bindZeroargMatches e1 e
    e2' <- bindZeroargMatches e2 e
    return $ EApp e1' e2'

data MatchState = Complete | Incomplete | Cons [(Idt, MatchState)] deriving (Eq, Ord, Show, Read)
