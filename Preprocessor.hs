module Preprocessor(getOps, getTypes, getInsts) where

import AbsPawel
import Data.Map hiding (map, filter)
import OpParser

isOpD :: Decl -> Bool 
isOpD (DLOp _ _ _) = True
isOpD (DROp _ _ _) = True
isOpD _ = False

isTypeD :: Decl -> Bool
isTypeD (DType _ _ _) = True
isTypeD _ = False

isExpD :: Decl -> Bool
isExpD (DExp _ _ _) = True
isExpD _ = False

getOpFormat :: Decl -> (Idt, (Idt, Integer, Integer))
getOpFormat (DLOp prec op sem) = (op, (sem, prec, 1))
getOpFormat (DROp prec op sem) = (op, (sem, prec, -1))

getOps :: Program -> Map Idt (Idt, Integer, Integer)
getOps (Prog ds) = fromList $ map getOpFormat $ filter isOpD ds

getTypeFormat :: Decl -> (Idt, ([Idt], [Variant]))
getTypeFormat (DType name vars variants) = (name, (vars, variants))

getTypes :: Program -> Map Idt ([Idt], [Variant])
getTypes (Prog ds) = fromList $ map getTypeFormat $ filter isTypeD ds

getInstFormat :: Decl -> (Idt, [TypeDecl], Exp)
getInstFormat (DExp name vars exp) = (name, vars, exp)

getInsts :: Program -> [(Idt, [TypeDecl], Exp)]
getInsts (Prog ds) = map getInstFormat $ filter isExpD ds