import Control.Monad.Reader
import Control.Monad.State
import Prelude hiding (lookup)
import Data.Map

type Var = String
data Exp = EInt Int
     | EOp  Op Exp Exp
     | EVar Var
     | ELet Var Exp Exp  -- let var = e1 in e2
     deriving (Eq, Show)

data Op = OpAdd | OpMul | OpSub deriving (Eq, Show)
type VarEnv = Map Var Int
type Store = Map Int Int

evalExp :: Exp -> Int
evalExp x = runReader (evalStateT (evalExp' x) empty) (empty)

evalExp' :: Exp -> (StateT Store (Reader VarEnv)) Int
evalExp' (EInt x) = return x
evalExp' (EOp OpAdd p q) = do
    v1 <- evalExp' p
    v2 <- evalExp' q
    return (v1 + v2)
evalExp' (EOp OpMul p q) = do
    v1 <- evalExp' p
    v2 <- evalExp' q
    return (v1 * v2)
evalExp' (EOp OpSub p q) = do
    v1 <- evalExp' p
    v2 <- evalExp' q
    return (v1 - v2)
evalExp' (ELet v e1 e2) = do
    v1 <- evalExp' e1
    e <- ask 
    s <- get
    let newloc = 1 + size s in do
        modify (\s -> insert newloc v1 s)
        local (\e -> insert v newloc e) (evalExp' e2)
evalExp' (EVar v) = do
    loc <- asks (\e -> fromMaybe (lookup v e))
    gets (\s -> fromMaybe (lookup loc s))

fromMaybe (Just x) = x

data BExp = EEq Exp Exp
    | EGreater Exp Exp
    | ETrue
    | EFalse

evalBExp' :: BExp -> (StateT Store (Reader VarEnv)) Bool
evalBExp' EFalse = return False
evalBExp' ETrue = return True
evalBExp' (EEq e1 e2) = do
    v1 <- evalExp' e1
    v2 <- evalExp' e2
    return (v1 == v2)
evalBExp' (EGreater e1 e2) = do
    v1 <- evalExp' e1
    v2 <- evalExp' e2
    return (v1 > v2)


data Stmt = SSkip
    | SAssign Var Exp
    | SSeq Stmt Stmt
    | SIf BExp Stmt Stmt
    | SWhile BExp Stmt
    | SDecl [Decl] Stmt

evalStmt :: Stmt -> Store
evalStmt x = runReader (execStateT (evalStmt' x) empty) empty

evalStmt' :: Stmt -> (StateT Store (Reader VarEnv)) ()
evalStmt' SSkip = return ()
evalStmt' (SAssign x ex) = do
    v <- evalExp' ex 
    env <- ask
    let loc = fromMaybe (lookup x env) in
        modify ( insert loc v )
evalStmt' (SSeq i1 i2) = do
    evalStmt' i1
    evalStmt' i2
evalStmt' (SIf b i1 i2) = do
    bval <- evalBExp' b
    if bval then evalStmt' i1 else evalStmt' i2
evalStmt' (SWhile b i) = do
    bval <- evalBExp' b
    if bval then evalStmt' (SSeq i (SWhile b i)) else return ()
evalStmt' (SDecl [] i) = evalStmt' i
evalStmt' (SDecl ((DVar v e):t) i) = do
    value <- evalExp' e
    s <- get
    let loc = 1 + size s in do
        modify (insert loc value)
        local (insert v loc) (evalStmt' (SDecl t i))

data Decl = DVar Var Exp

inst = SDecl [DVar "x" (EInt 5)]
            (SIf (EGreater (EVar "x") (EInt 2)) (SAssign "x" (EInt 3)) (SAssign "x" (EInt 10)))
