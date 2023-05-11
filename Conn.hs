module Conn where

import ParPawel   ( pProgram, myLexer )
import Calc
import AbsPawel
import Binder
import OpParser
import Preprocessor
import MatchChecker
import Control.Monad.Reader
import Control.Monad.Except
import Inference
import System.IO
import System.Environment
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

aenv = inserts [(Idt "{-}", ari $ ariOp (-)), 
                (Idt "{*}", ari $ ariOp (*)),
                (Idt "{+}", ari $ ariOp (+)), 
                (Idt "{/}", ari $ AriOp (\x y -> if y /= 0 then Just $ x `div` y else Nothing)),
                (Idt "{>}", ari $ ariOp (\x y -> if x > y then 1 else 0)),
                (Idt "{<}", ari $ ariOp (\x y -> if x < y then 1 else 0)),
                (Idt "{>=}", ari $ ariOp (\x y -> if x >= y then 1 else 0)),
                (Idt "{<=}", ari $ ariOp (\x y -> if x <= y then 1 else 0)),
                (Idt "{==}", ari $ ariOp (\x y -> if x == y then 1 else 0))] Map.empty

atenv = inserts [(Idt "{-}", Scheme [] $ TFunc TInt (TFunc TInt TInt)), 
                 (Idt "{*}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
                 (Idt "{+}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
                 (Idt "{/}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
                 (Idt "{>}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
                 (Idt "{<}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
                 (Idt "{>=}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
                 (Idt "{<=}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
                 (Idt "{==}", Scheme [] $ TFunc TInt (TFunc TInt TInt))] Map.empty

cc x = runReaderT (calc x) aenv
bb x fname = runReaderT (bind x) (Map.insert (Idt fname) (EBVar $ Idt fname) aenv)

getInts :: Map.Map Idt (Either String ExpBound) -> [(Idt, [Integer])]
getInts m = [(k, h:t) | (k, Just (h:t)) <- Map.toList $ Map.map f m] where
    f (Right (EBOverload [])) = return []
    f (Right (EBOverload ((EBInt x):xs))) = fmap (x:) $ f (Right $ EBOverload xs)
    f (Right (EBOverload (x:xs))) = f (Right $ EBOverload xs)
    f (Right (EBInt x)) = return [x]
    f _ = Nothing

type FullEnv = (BEnv, Map.Map Idt Scheme, VariantEnv, Map.Map Idt (Idt, Integer, Integer))

processDecl :: FullEnv -> Decl -> Except String FullEnv
processDecl (env, tenv, venv, ops) (DExp name tds exp) = let unbound = (ELet name tds (infixate exp ops) (EVar name)) in
    if is_typed tds then
        let bound = bindRecurrent (bindZeroargMatches unbound (venv, tenv)) name env 
            current = case Map.lookup name tenv of
                Just (Scheme vars t) -> t
                Nothing -> TOverload [] in do
                    (boundType, exps) <- overloadInference tenv venv bound name 
                    calcedExp <- runReaderT (calc exps) env
                    let fullScheme = generalize (TypeEnv tenv) (sumTypes current boundType)
                        bounds = expToList calcedExp in
                        case Map.lookup name env of
                            Just (EBOverload xs) -> 
                                return (
                                    Map.insert name (EBOverload $ xs ++ bounds) env, 
                                    Map.insert name fullScheme tenv,
                                    venv,
                                    ops
                                )
                            _ -> 
                                return (
                                    Map.insert name (EBOverload bounds) env, 
                                    Map.insert name fullScheme tenv,
                                    venv,
                                    ops
                                )
    else
        let bound = bindRecurrent (bindZeroargMatches unbound (venv, tenv)) name env in do {
            (typeAssignment, exps) <- overloadInference tenv venv bound name;
            calcedExp <- runReaderT (calc exps) env;
            return (
                Map.insert name calcedExp env, 
                Map.insert name (generalize (TypeEnv tenv) typeAssignment) tenv, 
                venv,
                ops
            )
        }
processDecl envs (DType name tvs []) = return envs
processDecl (env, tenv, venv, ops) (DType name tvs ((VarType vname ts):t)) = 
    if all (flip elem tvs) (Set.elems $ ftv $ TVariant vname ts) then processDecl (
            let tng [] n = []
                tng (h:t) n = (Idt $ "a" ++ show n):tng t (n+1) 
                foldFuncs [] acc = acc
                foldFuncs (h:t) acc = TFunc h (foldFuncs t acc) 
                tns = tng ts 0 in
                (
                    Map.insert vname (EBLam Map.empty tns (EBVariant vname (map EBVar tns))) env,
                    Map.insert vname (Scheme tvs $ foldFuncs ts $ TVariant name (map TVar tvs)) tenv,
                    insertCons vname (Scheme tvs $ TVariant name (map TVar tvs)) venv,
                    ops
                )
        ) (DType name tvs t)
    else error "Unbound type variable in type definition"
processDecl (env, tenv, venv, ops) (DLOp prec op sem) = return (env, tenv, venv, Map.insert op (sem, prec, -1) ops)
processDecl (env, tenv, venv, ops) (DROp prec op sem) = return (env, tenv, venv, Map.insert op (sem, prec,  1) ops)

str_to_calc :: String -> Except String String
str_to_calc x = case pProgram (myLexer x) of
    Left err -> throwError err
    Right (Prog es) -> let envs = foldM processDecl (aenv, atenv, emptyEnv, Map.fromList bop) es in do
        (env, tenv, venv, ops) <- envs       
        return $ (show tenv) ++ "\n\n===============\n\n" ++ 
            (show env) ++ "\n\n========================\n\n" ++ 
            (show venv) ++ "\n\n========================\n\n" ++
            (show $ Map.map (\x -> runExcept (runReaderT (calc x) env)) env) ++ "\n\n========================\n\n" ++
            (show $ getInts $ Map.map (\x -> runExcept (runReaderT (calc x) env)) env) where
        

runProgram :: FullEnv -> String -> Except String FullEnv
runProgram envs x = case pProgram (myLexer x) of
    Left err -> throwError err
    Right (Prog es) -> foldM (\x -> processDecl x) envs es    

main :: IO ()
main = do
    args <- getArgs
    case args of
        [fname] -> do
            file <- readFile fname
            case runExcept $ str_to_calc file of
                Left err -> hPutStrLn stderr err
                Right res -> putStrLn res
        _ ->
            let inputloop = do {
                putStr "Paweł> ";
                hFlush stdout;
                line <- getLine;
                case line of
                    ":q" -> return ""
                    _ -> do
                        rest <- inputloop
                        return $ line ++ "\n" ++ rest
            } in do
                putStrLn "Welcome to Paweł!"
                putStrLn "Type :q to quit"
                unparsed <- inputloop
                case runExcept $ str_to_calc unparsed of
                    Left err -> putStrLn err
                    Right res -> putStrLn res
                