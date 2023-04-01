import Data.Map

type PName = String

data Exp = EName PName
    | EAppUnparsed [Exp]
    | EApp Exp Exp
    | EAbs PName Exp
    | EInt Int
    | EOp PName Exp Exp
    deriving (Eq, Show)

ops :: Map PName (PName, Int, Int)
ops = fromList [("+", ("plus", 5, 1)), ("/", ("divide", 7, 1)), (",", ("cons", 3, -1))]

isOp :: Exp -> Bool
isOp (EName x) = member x ops
isOp _ = False

name :: Exp -> PName
name (EName x) = x
name _ = error "name: not a name"

first (x, _, _) = x

infixate :: Exp -> Exp
infixate (EAppUnparsed es) = infixateOps es
infixate (EApp e1 e2) = EApp (infixate e1) (infixate e2)
infixate (EAbs x e) = EAbs x (infixate e)
infixate (EOp x e1 e2) = EOp x (infixate e1) (infixate e2)
infixate (EInt x) = EInt x
infixate (EName x) = EName x

infixateOps :: [Exp] -> Exp
infixateOps [] = error "infixateOps: empty list"
infixateOps [e] = if isOp e then error "operator without arguments" else infixate e
infixateOps [e1, e2] = if isOp e1 || isOp e2 then error "operator without arguments" else EApp (infixate e1) (infixate e2)
infixateOps [e1, e2, e3] = 
    if isOp e2 then 
        EApp (EApp (EName (first $ ops ! (name e2))) (infixate e1)) (infixate e3) 
    else 
        infixateOps [(infixateOps [e1, e2]), e3]
infixateOps [e1, e2, e3, e4] = 
    if isOp e2 then 
        EApp (EApp (EName (first $ ops ! (name e2))) (infixate e1)) (infixateOps [e3, e4]) 
    else
        infixateOps [(infixateOps [e1, e2]), e3, e4]
infixateOps (e1:e2:e3:e4:es) =
    if isOp e2 && isOp e4 then 
        let (op1, prec1, add1) = ops ! (name e2)
            (op2, prec2, add2) = ops ! (name e4)
        in if 2 * prec1 + add1 < 2 * prec2 then
            EApp (EApp (EName op1) (infixate e1)) (infixateOps (e3:e4:es))
        else
            EApp (EApp (EName op2) (infixateOps [e1, e2, e3])) (infixateOps es)
    else if isOp e2 then
        EApp (EApp (EName (first $ ops ! (name e2))) (infixate e1)) (infixateOps (e3:e4:es))
    else if isOp e4 then
        EApp (EApp (EName (first $ ops ! (name e4))) (infixateOps [e1, e2, e3])) (infixateOps es)
    else
        infixateOps $ (infixateOps [e1, e2]) : e3 : e4 : es