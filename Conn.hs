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

-- getInts :: Map.Map Idt (Either Integer ExpBound) -> Map.Map Idt Integer
getInts m = [(k, x) | (k, Left x) <- Map.toList $ Map.map f m] where
-- getInts = id where
    f (Right (EBOverload [])) = Right $ EBVar $ Idt "_"
    f (Right (EBOverload ((EBInt x):xs))) = Left x
    f (Right (EBOverload (x:xs))) = f (Right (EBOverload xs))
    f x = x

str_to_calc :: String -> String
str_to_calc x = case pProgram (myLexer x) of
    Left err -> err
    Right (Prog es) -> (show tenv) ++ "\n\n===============\n\n" ++ (show $ getInts $ Map.map (\x -> runReader (calc x) env) env) where
        ops = inserts bop (getOps (Prog es))
        (env, tenv) = foldl f (aenv, atenv) es
        f (env, tenv) (DExp name tds exp) = let unbound = (ELam (map untype tds) $ infixate exp ops) in
            if is_typed tds then
                let bound = bindRecurrent unbound name env 
                    current = case Map.lookup name tenv of
                        Just (Scheme vars t) -> t
                        Nothing -> TOverload []
                    boundType = overloadInference tenv bound name 
                    fullScheme = generalize (TypeEnv tenv) (sumTypes current boundType) in
                    case Map.lookup name env of
                        Just (EBOverload xs) -> 
                            let bounds = expToList $ makeOverloadsRecurrent (length xs) name bound in
                                (
                                    Map.insert name (EBOverload $ xs ++ bounds) env, 
                                    Map.insert name fullScheme tenv
                                )
                        _ -> 
                            let bounds = expToList $ makeOverloadsRecurrent 0 name bound in
                                (
                                    Map.insert name (EBOverload bounds) env, 
                                    Map.insert name fullScheme tenv
                                )
            else
                let bound = bindRecurrent unbound name env
                    typeAssignment = overloadInference tenv bound name
                    recOver = case bound of
                        EBOverload _ -> makeOverloadsRecurrent 0 name bound 
                        _ -> bound in
                (Map.insert name recOver env, Map.insert name (generalize (TypeEnv tenv) typeAssignment) tenv)
        f envs (DType name tvs []) = envs
        f (env, tenv) (DType name tvs ((VarType vname ts):t)) = f (
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
        f envs _ = envs

main :: IO ()
main = interact str_to_calc