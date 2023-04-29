module OpParser where

import Data.Map hiding (map)
import AbsPawel

type OpEnv = Map Idt (Idt, Integer, Integer) 

isOp :: Exp -> OpEnv -> Bool
isOp (EVar x) ops = member x ops
isOp _ _ = False

isOpM :: Match -> OpEnv -> Bool
isOpM (MVar x) ops = member x ops
isOpM _ _ = False

name :: Exp -> Idt
name (EVar x) = x
name _ = error "name: not a name"

nameM :: Match -> Idt
nameM (MVar x) = x
nameM _ = error "nameM: not a name"

first (x, _, _) = x

infixate :: Exp -> OpEnv -> Exp
infixate (EUnparsed es) ops = infixateOps es ops 
infixate (EApp e1 e2) ops = EApp (infixate e1 ops) (infixate e2 ops)
infixate (ELam x e) ops = ELam x (infixate e ops)
infixate (EInt x) ops = EInt x
infixate (EVar x) ops = EVar x
infixate (ELet x tds e1 e2) ops = ELet x tds (infixate e1 ops) (infixate e2 ops)
infixate (EIf e1 e2 e3) ops = EIf (infixate e1 ops) (infixate e2 ops) (infixate e3 ops)
infixate (EMatch x ms) ops = EMatch x (map (\(Case m e) -> Case (infixateMatch m ops) (infixate e ops)) ms)

infixateMatch :: Match -> OpEnv -> Match
infixateMatch (MVar x) ops = MVar x
infixateMatch (MList ms) ops = infixateMatchOps ms ops
infixateMatch (MCons x ms) ops = MCons x (map (flip infixateMatch ops) ms)

infixateOps :: [Exp] -> OpEnv -> Exp
infixateOps [] ops = error "infixateOps: empty list"
infixateOps [e] ops = if isOp e ops then error "operator without arguments" else infixate e ops
infixateOps [e1, e2] ops = if isOp e1 ops || isOp e2 ops then error "operator without arguments" 
    else EApp (infixate e1 ops) (infixate e2 ops)
infixateOps [e1, e2, e3] ops = 
    if isOp e2 ops then 
        EApp (EApp (EVar (first $ ops ! (name e2))) (infixate e1 ops)) (infixate e3 ops) 
    else 
        infixateOps [(infixateOps [e1, e2] ops), e3] ops
infixateOps [e1, e2, e3, e4] ops = 
    if isOp e2 ops then 
        EApp (EApp (EVar (first $ ops ! (name e2))) (infixate e1 ops)) (infixateOps [e3, e4] ops) 
    else
        infixateOps [(infixateOps [e1, e2] ops), e3, e4] ops
infixateOps (e1:e2:e3:e4:es) ops =
    if isOp e2 ops && isOp e4 ops then 
        let (op1, prec1, add1) = ops ! (name e2)
            (op2, prec2, add2) = ops ! (name e4)
        in if 2 * prec1 + add1 < 2 * prec2 then
            EApp (EApp (EVar op1) (infixate e1 ops)) (infixateOps (e3:e4:es) ops)
        else
            EApp (EApp (EVar op2) (infixateOps [e1, e2, e3] ops)) (infixateOps es ops)
    else if isOp e2 ops then
        EApp (EApp (EVar (first $ ops ! (name e2))) (infixate e1 ops)) (infixateOps (e3:e4:es) ops)
    else if isOp e4 ops then
        EApp (EApp (EVar (first $ ops ! (name e4))) (infixateOps [e1, e2, e3] ops)) (infixateOps es ops)
    else
        infixateOps ((infixateOps [e1, e2] ops) : e3 : e4 : es) ops

infixateMatchOps :: [Match] -> OpEnv -> Match
infixateMatchOps [] ops = error "infixateMatchOps: empty list"
infixateMatchOps [m] ops = if isOpM m ops then error "operator without arguments" else infixateMatch m ops
infixateMatchOps [m1, m2] ops = if isOpM m1 ops || isOpM m2 ops then error "operator without arguments" 
    else MCons (nameM m1) [infixateMatch m2 ops]
infixateMatchOps (m1:m2:ms) ops =
    if isOpM m2 ops then
        MCons (first $ ops ! (nameM m2)) [infixateMatch m1 ops, infixateMatchOps ms ops]
    else
        MCons (nameM m1) (map (flip infixateMatch ops) (m2:ms))