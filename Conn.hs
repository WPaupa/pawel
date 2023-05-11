module Conn where

import ParPawel   ( pProgram, myLexer )
import Calc
import AbsPawel
import Binder
import OpParser
import Preprocessor
import Control.Monad.Reader
import Inference
import qualified Data.Map as Map
import qualified Data.Set as Set

is_typed :: [TypeDecl] -> Bool
is_typed [] = False
is_typed ((TDVar _):t) = is_typed t
is_typed ((TDType _ _):t) = True

isLeft :: Either a b -> Bool
isLeft (Left a) = True
isLeft (Right a) = False

fromLeft :: Either a b -> a
fromLeft (Left a) = a

expToList :: ExpBound -> [ExpBound]
expToList (EBOverload xs) = xs
expToList x = [x]

bop = [(Idt "+", (Idt "{+}", 5, 1)), 
       (Idt "-", (Idt "{-}", 5, 1)),
       (Idt "/", (Idt "{/}", 7, 1)),
       (Idt "*", (Idt "{*}", 7, 1)), 
       (Idt ",", (Idt "Cons", 3, -1))]

aenv = inserts [(Idt "{-}", EBLam Map.empty [Idt "x", Idt "y"] $ EBArith (EBVar $ Idt "x") (EBVar $ Idt "y") $ AriOp (-)), 
                (Idt "{*}", EBLam Map.empty [Idt "x", Idt "y"] $ EBArith (EBVar $ Idt "x") (EBVar $ Idt "y") $ AriOp (*)),
                (Idt "{+}", EBLam Map.empty [Idt "x", Idt "y"] $ EBArith (EBVar $ Idt "x") (EBVar $ Idt "y") $ AriOp (+)), 
                (Idt "{/}", EBLam Map.empty [Idt "x", Idt "y"] $ EBArith (EBVar $ Idt "x") (EBVar $ Idt "y") $ AriOp (\x y -> x `div` y)),
                (Idt "{>}", EBLam Map.empty [Idt "x", Idt "y"] $ EBArith (EBVar $ Idt "x") (EBVar $ Idt "y") $ AriOp (\x y -> if x > y then 1 else 0)),
                (Idt "{<}", EBLam Map.empty [Idt "x", Idt "y"] $ EBArith (EBVar $ Idt "x") (EBVar $ Idt "y") $ AriOp (\x y -> if x < y then 1 else 0)),
                (Idt "{>=}", EBLam Map.empty [Idt "x", Idt "y"] $ EBArith (EBVar $ Idt "x") (EBVar $ Idt "y") $ AriOp (\x y -> if x >= y then 1 else 0)),
                (Idt "{<=}", EBLam Map.empty [Idt "x", Idt "y"] $ EBArith (EBVar $ Idt "x") (EBVar $ Idt "y") $ AriOp (\x y -> if x <= y then 1 else 0)),
                (Idt "{==}", EBLam Map.empty [Idt "x", Idt "y"] $ EBArith (EBVar $ Idt "x") (EBVar $ Idt "y") $ AriOp (\x y -> if x == y then 1 else 0))] Map.empty

atenv = inserts [(Idt "{-}", Scheme [] $ TFunc TInt (TFunc TInt TInt)), 
                 (Idt "{*}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
                 (Idt "{+}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
                 (Idt "{/}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
                 (Idt "{>}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
                 (Idt "{<}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
                 (Idt "{>=}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
                 (Idt "{<=}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
                 (Idt "{==}", Scheme [] $ TFunc TInt (TFunc TInt TInt))] Map.empty

cc x = runReader (calc x) aenv
bb x fname = runReader (bind x) (Map.insert (Idt fname) (EBVar $ Idt fname) aenv)

getInts :: Map.Map Idt ExpBound -> [(Idt, [Integer])]
getInts m = [(k, h:t) | (k, Just (h:t)) <- Map.toList $ Map.map f m] where
    f (EBOverload []) = return []
    f (EBOverload ((EBInt x):xs)) = fmap (x:) $ f (EBOverload xs)
    f (EBOverload (x:xs)) = f (EBOverload xs)
    f (EBInt x) = return [x]
    f _ = Nothing

str_to_calc :: String -> String
str_to_calc x = case pProgram (myLexer x) of
    Left err -> err
    Right (Prog es) -> (show tenv) ++ "\n\n===============\n\n" ++ 
        (show env) ++ "\n\n========================\n\n" ++ 
        (show $ Map.map (\x -> runReader (calc x) env) env) ++ "\n\n========================\n\n" ++
        (show $ getInts $ Map.map (\x -> runReader (calc x) env) env) where
        ops = inserts bop (getOps (Prog es))
        (env, tenv) = foldl f (aenv, atenv) es
        f (env, tenv) (DExp name tds exp) = let unbound = (ELet name tds (infixate exp ops) (EVar name)) in
            if is_typed tds then
                let bound = bindRecurrent unbound name env 
                    current = case Map.lookup name tenv of
                        Just (Scheme vars t) -> t
                        Nothing -> TOverload []
                    (boundType, exps) = overloadInference tenv bound name 
                    fullScheme = generalize (TypeEnv tenv) (sumTypes current boundType)
                    bounds = expToList exps in
                    case Map.lookup name env of
                        Just (EBOverload xs) -> 
                            (
                                Map.insert name (EBOverload $ xs ++ bounds) env, 
                                Map.insert name fullScheme tenv
                            )
                        _ -> 
                            (
                                Map.insert name (EBOverload bounds) env, 
                                Map.insert name fullScheme tenv
                            )
            else
                let bound = bindRecurrent unbound name env
                    (typeAssignment, exps) = overloadInference tenv bound name in
                (Map.insert name exps env, Map.insert name (generalize (TypeEnv tenv) typeAssignment) tenv)
        f envs (DType name tvs []) = envs
        f (env, tenv) (DType name tvs ((VarType vname ts):t)) = 
            if all (flip elem tvs) (Set.elems $ ftv $ TVariant vname ts) then f (
                    let tng [] n = []
                        tng (h:t) n = (Idt $ "a" ++ show n):tng t (n+1) 
                        foldFuncs [] acc = acc
                        foldFuncs (h:t) acc = TFunc h (foldFuncs t acc) 
                        tns = tng ts 0 in
                        (
                            Map.insert vname (EBLam Map.empty tns (EBVariant vname (map EBVar tns))) env,
                            Map.insert vname (Scheme tvs $ foldFuncs ts $ TVariant name ts) tenv
                        )
                ) (DType name tvs t)
            else error "Unbound type variable in type definition"
        f envs _ = envs

main :: IO ()
main = interact str_to_calc