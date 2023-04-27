module OpParser where

import Data.Map hiding (map)
import AbsPawel

ops :: Map Idt (Idt, Integer, Integer)
ops = fromList [(Idt "+", (Idt "plus", 5, 1)), (Idt "/", (Idt "divide", 7, 1)), (Idt ",", (Idt "cons", 3, -1))]

isOp :: Exp -> Bool
isOp (EVar x) = member x ops
isOp _ = False

isOpM :: Match -> Bool
isOpM (MVar x) = member x ops
isOpM _ = False

name :: Exp -> Idt
name (EVar x) = x
name _ = error "name: not a name"

nameM :: Match -> Idt
nameM (MVar x) = x
nameM _ = error "nameM: not a name"

first (x, _, _) = x

infixate :: Exp -> Exp
infixate (EUnparsed es) = infixateOps es
infixate (EApp e1 e2) = EApp (infixate e1) (infixate e2)
infixate (ELam x e) = ELam x (infixate e)
infixate (EInt x) = EInt x
infixate (EVar x) = EVar x
infixate (ELet x tds e1 e2) = ELet x tds (infixate e1) (infixate e2)
infixate (EIf e1 e2 e3) = EIf (infixate e1) (infixate e2) (infixate e3)
infixate (EMatch x ms) = EMatch x (map (\(Case m e) -> Case (infixateMatch m) (infixate e)) ms)

infixateMatch :: Match -> Match
infixateMatch (MVar x) = MVar x
infixateMatch (MList ms) = infixateMatchOps ms
infixateMatch (MCons x ms) = MCons x (map infixateMatch ms)

infixateOps :: [Exp] -> Exp
infixateOps [] = error "infixateOps: empty list"
infixateOps [e] = if isOp e then error "operator without arguments" else infixate e
infixateOps [e1, e2] = if isOp e1 || isOp e2 then error "operator without arguments" else EApp (infixate e1) (infixate e2)
infixateOps [e1, e2, e3] = 
    if isOp e2 then 
        EApp (EApp (EVar (first $ ops ! (name e2))) (infixate e1)) (infixate e3) 
    else 
        infixateOps [(infixateOps [e1, e2]), e3]
infixateOps [e1, e2, e3, e4] = 
    if isOp e2 then 
        EApp (EApp (EVar (first $ ops ! (name e2))) (infixate e1)) (infixateOps [e3, e4]) 
    else
        infixateOps [(infixateOps [e1, e2]), e3, e4]
infixateOps (e1:e2:e3:e4:es) =
    if isOp e2 && isOp e4 then 
        let (op1, prec1, add1) = ops ! (name e2)
            (op2, prec2, add2) = ops ! (name e4)
        in if 2 * prec1 + add1 < 2 * prec2 then
            EApp (EApp (EVar op1) (infixate e1)) (infixateOps (e3:e4:es))
        else
            EApp (EApp (EVar op2) (infixateOps [e1, e2, e3])) (infixateOps es)
    else if isOp e2 then
        EApp (EApp (EVar (first $ ops ! (name e2))) (infixate e1)) (infixateOps (e3:e4:es))
    else if isOp e4 then
        EApp (EApp (EVar (first $ ops ! (name e4))) (infixateOps [e1, e2, e3])) (infixateOps es)
    else
        infixateOps $ (infixateOps [e1, e2]) : e3 : e4 : es

infixateMatchOps :: [Match] -> Match
infixateMatchOps [] = error "infixateMatchOps: empty list"
infixateMatchOps [m] = if isOpM m then error "operator without arguments" else infixateMatch m
infixateMatchOps [m1, m2] = if isOpM m1 || isOpM m2 then error "operator without arguments" 
    else MCons (nameM m1) [infixateMatch m2]
infixateMatchOps (m1:m2:ms) =
    if isOpM m2 then
        MCons (first $ ops ! (nameM m2)) [infixateMatch m1, infixateMatchOps ms]
    else
        MCons (nameM m1) (map infixateMatch (m2:ms))