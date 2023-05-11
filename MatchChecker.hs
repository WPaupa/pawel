module MatchChecker where
import Control.Monad.Reader
import Control.Monad.Except
import Prelude hiding (lookup)
import Data.Map hiding (map, foldl, filter)
import AbsPawel

type VariantEnv = (Map Idt Scheme, Map Idt [Idt])
insertCons :: Idt -> Scheme -> VariantEnv -> VariantEnv
insertCons name t@(Scheme _ (TVariant tname _)) (a, b) = (insert name t a, insertWith (++) tname [name] b)

emptyEnv :: VariantEnv
emptyEnv = (empty, empty)

bindZeroargMatches :: Exp -> (VariantEnv, Map Idt Scheme) -> Exp
bindZeroargMatches (EVar x) e = EVar x
bindZeroargMatches (EInt x) e = EInt x
bindZeroargMatches (ELet x tds e1 e2) e = ELet x tds (bindZeroargMatches e1 e) (bindZeroargMatches e2 e)
bindZeroargMatches (EIf e1 e2 e3) e = EIf (bindZeroargMatches e1 e) (bindZeroargMatches e2 e) (bindZeroargMatches e3 e)
bindZeroargMatches (ELam xs ex) e = ELam xs (bindZeroargMatches ex e)
bindZeroargMatches (EMatch x cases) e@((ve, _), te) = 
    let bindMatch (MVar x) = if member x ve then case lookup x te of
                Just (Scheme _ (TVariant _ _)) -> MCons x []
                _ -> MVar x
            else MVar x
        bindMatch (MCons name xs) = MCons name (map bindMatch xs) in
        EMatch x (map (\(Case c ex) -> Case (bindMatch c) (bindZeroargMatches ex e)) cases)
bindZeroargMatches (EApp e1 e2) e = EApp (bindZeroargMatches e1 e) (bindZeroargMatches e2 e)

data MatchState = Complete | Incomplete | Cons [(Idt, MatchState)] deriving (Eq, Ord, Show, Read)
