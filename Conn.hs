module Conn where

import ParPawel   ( pProgram, myLexer )
import Calc
import AbsPawel
import Binder
import OpParser
import Preprocessor
import Control.Monad.Reader
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
    Right (Prog es) -> (show env) ++ "\n\n===============\n\n" ++ (show $ getInts $ Map.map (\x -> runReader (calc x) env) env) where
        ops = inserts bop (getOps (Prog es))
        env = foldl f aenv es
        f env (DExp name@(Idt fname) tds exp) = let unbound = (ELam (map untype tds) $ infixate exp ops) in
            if is_typed tds then
                let bound = bba unbound fname env in
                    case Map.lookup name env of
                        Just (EBOverload xs) -> Map.insert name (EBOverload $ bound:xs) env
                        _ -> Map.insert name (EBOverload [bound]) env
            else
                extend unbound fname env
        f env (DType name tvs []) = env
        f env (DType name tvs ((VarType vname ts):t)) = f (
                let tns = map (Idt . show) ts 
                    expify [] xs = EBVariant vname (reverse xs)
                    expify (h:t) xs = EBCons (FWCons $ \e -> expify t (e:xs)) in
                    Map.insert vname (expify tns []) env
            ) (DType name tvs t)
        f env _ = env

main :: IO ()
main = interact str_to_calc