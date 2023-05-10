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


bop = [(Idt "+", (Idt "{+}", 5, 1)), 
       (Idt "-", (Idt "{-}", 5, 1)),
       (Idt "/", (Idt "{/}", 7, 1)),
       (Idt "*", (Idt "{*}", 7, 1)), 
       (Idt ",", (Idt "Cons", 3, -1))]

-- getInts :: Map.Map Idt (Either Integer ExpBound) -> Map.Map Idt Integer
getInts = (Map.map fromLeft) . (Map.filter isLeft) . (Map.map f) where
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
        (env, tenv) = foldl f (aenv, Map.empty) es
        f (env, tenv) (DExp name tds exp) = let unbound = (ELam (map untype tds) $ infixate exp ops) in
            if is_typed tds then
                let bound = bindRecurrent unbound name env in
                    case Map.lookup name env of
                        Just (EBOverload xs) -> (Map.insert name (EBOverload $ bound:xs) env, tenv)
                        _ -> (Map.insert name (EBOverload [bound]) env, tenv)
            else
                (extend unbound name env, tenv)
        f envs (DType name tvs []) = envs
        f (env, tenv) (DType name tvs ((VarType vname ts):t)) = f (
                let tng [] n = []
                    tng (h:t) n = (Idt $ "a" ++ show n):tng t (n+1) 
                    foldFuncs [] acc = acc
                    foldFuncs (h:t) acc = TFunc (TVar h) (foldFuncs t acc) 
                    tns = tng ts 0 in
                    (
                        Map.insert vname (EBLam Map.empty tns (EBVariant vname (map EBVar tns))) env,
                        Map.insert vname (Scheme tvs $ TVariant name ts) tenv
                    )
            ) (DType name tvs t)
        f envs _ = envs

main :: IO ()
main = interact str_to_calc