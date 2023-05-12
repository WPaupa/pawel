module OpParser where

import AbsPawel
import Control.Monad.Except
import Data.Map hiding (map)

type OpEnv = Map Idt (Idt, Integer, Integer)

isOp :: Exp -> OpEnv -> Bool
isOp (EVar x) ops = member x ops
isOp _ _ = False

isOpM :: Match -> OpEnv -> Bool
isOpM (MVar x) ops = member x ops
isOpM _ _ = False

name :: Exp -> Except String Idt
name (EVar x) = return x
name _ = throwError "name: not a name"

nameM :: Match -> Except String Idt
nameM (MVar x) = return x
nameM _ = throwError "nameM: not a name"

first (x, _, _) = x

infixate :: Exp -> OpEnv -> Except String Exp
infixate (EUnparsed es) ops = infixateOps es ops
infixate (EApp e1 e2) ops = do
    e1' <- infixate e1 ops
    e2' <- infixate e2 ops
    return $ EApp e1' e2'
infixate (ELam x e) ops = do
    e' <- infixate e ops
    return $ ELam x e'
infixate (EInt x) ops = return $ EInt x
infixate (EVar x) ops = return $ EVar x
infixate (ELet x tds e1 e2) ops = do
    e1' <- infixate e1 ops
    e2' <- infixate e2 ops
    return $ ELet x tds e1' e2'
infixate (EIf e1 e2 e3) ops = do
    e1' <- infixate e1 ops
    e2' <- infixate e2 ops
    e3' <- infixate e3 ops
    return $ EIf e1' e2' e3'
infixate (EMatch x ms) ops =
    fmap
        (EMatch x)
        (mapM
            ( \(Case m e) -> do
                m' <- infixateMatch m ops
                e' <- infixate e ops
                return $ Case m' e'
            )
            ms
        )

infixateMatch :: Match -> OpEnv -> Except String Match
infixateMatch (MVar x) ops = return $ MVar x
infixateMatch (MList ms) ops = infixateMatchOps ms ops
infixateMatch (MCons x ms) ops = fmap (MCons x) (mapM (flip infixateMatch ops) ms)

infixateOps :: [Exp] -> OpEnv -> Except String Exp
infixateOps [] ops = throwError "Empty expression"
infixateOps [e] ops = if isOp e ops then throwError "operator without arguments" else infixate e ops
infixateOps [e1, e2] ops =
    if isOp e1 ops || isOp e2 ops
        then throwError "operator without arguments"
        else do
            e1' <- infixate e1 ops
            e2' <- infixate e2 ops
            return $ EApp e1' e2'
infixateOps [e1, e2, e3] ops =
    if isOp e2 ops
        then do
            e1' <- infixate e1 ops
            e2' <- name e2
            e3' <- infixate e3 ops
            return $ EApp (EApp (EVar (first $ ops ! e2')) e1') e3'
        else do
            e12' <- infixateOps [e1, e2] ops
            infixateOps [e12', e3] ops
infixateOps [e1, e2, e3, e4] ops =
    if isOp e2 ops
        then do
            e1' <- infixate e1 ops
            e2' <- name e2
            e34' <- infixateOps [e3, e4] ops
            return $ EApp (EApp (EVar (first $ ops ! e2')) e1') e34'
        else do
            e12' <- infixateOps [e1, e2] ops
            infixateOps [e12', e3, e4] ops
infixateOps (e1 : e2 : e3 : e4 : es) ops =
    if isOp e2 ops && isOp e4 ops
        then do
            e2' <- name e2
            e4' <- name e4
            let (op1, prec1, add1) = ops ! e2'
                (op2, prec2, add2) = ops ! e4'
             in if 2 * prec1 + add1 < 2 * prec2
                    then do
                        e1' <- infixate e1 ops
                        e34s' <- infixateOps (e3 : e4 : es) ops
                        return $ EApp (EApp (EVar op1) e1') e34s'
                    else do
                        e123' <- infixateOps [e1, e2, e3] ops
                        es' <- infixateOps es ops
                        return $ EApp (EApp (EVar op2) e123') es'
    else if isOp e2 ops
        then do
            e1' <- infixate e1 ops
            e2' <- name e2
            e34s' <- infixateOps (e3 : e4 : es) ops
            return $ EApp (EApp (EVar (first $ ops ! e2')) e1') e34s'
    else if isOp e4 ops
        then do
            e123' <- infixateOps [e1, e2, e3] ops
            e4' <- name e4
            es' <- infixateOps es ops
            return $ EApp (EApp (EVar (first $ ops ! e4')) e123') es'
        else do
            e12' <- infixateOps [e1, e2] ops
            infixateOps (e12' : e3 : e4 : es) ops

infixateMatchOps :: [Match] -> OpEnv -> Except String Match
infixateMatchOps [] ops = throwError "Empty match"
infixateMatchOps [m] ops = if isOpM m ops then throwError "operator without arguments" else infixateMatch m ops
infixateMatchOps [m1, m2] ops =
    if isOpM m1 ops || isOpM m2 ops
        then throwError "operator without arguments"
        else do
            m1' <- nameM m1
            m2' <- infixateMatch m2 ops
            return $ MCons m1' [m2']
infixateMatchOps (m1 : m2 : ms) ops =
    if isOpM m2 ops
        then do
            m1' <- infixateMatch m1 ops
            m2' <- nameM m2
            ms' <- infixateMatchOps ms ops
            return $ MCons (first $ ops ! m2') [m1', ms']
        else do
            m1' <- nameM m1
            fmap (MCons m1') (mapM (flip infixateMatch ops) (m2 : ms))