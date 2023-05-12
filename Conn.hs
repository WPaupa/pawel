module Conn where

import AbsPawel
import Binder
import Calc
import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Inference
import MatchChecker
import OpParser
import ParPawel (myLexer, pProgram)
import System.Environment
import System.IO

is_typed :: [TypeDecl] -> Bool
is_typed [] = False
is_typed ((TDVar _) : t) = is_typed t
is_typed ((TDType _ _) : t) = True

isLeft :: Either a b -> Bool
isLeft (Left a) = True
isLeft (Right a) = False

fromLeft :: Either a b -> a
fromLeft (Left a) = a

expToList :: ExpBound -> [ExpBound]
expToList (EBOverload xs) = xs
expToList x = [x]

bop =
    [ (Idt "$", (Idt "{$}", 0, -1)),
      (Idt "||", (Idt "{||}", 2, -1)),
      (Idt "&&", (Idt "{&&}", 3, -1)),
      (Idt "==", (Idt "{==}", 4, -1)),
      (Idt "/=", (Idt "{/=}", 4, -1)),
      (Idt "<", (Idt "{<}", 4, -1)),
      (Idt ">", (Idt "{>}", 4, -1)),
      (Idt "<=", (Idt "{<=}", 4, -1)),
      (Idt ">=", (Idt "{>=}", 4, -1)),
      (Idt ",", (Idt "Cons", 0, -1)),
      (Idt ":", (Idt "Cons", 5, -1)),
      (Idt "++", (Idt "{++}", 5, -1)),
      (Idt "+", (Idt "{+}", 6, 1)),
      (Idt "-", (Idt "{-}", 6, 1)),
      (Idt "/", (Idt "{/}", 7, 1)),
      (Idt "*", (Idt "{*}", 7, 1)),
      (Idt "^", (Idt "{^}", 8, -1))
    ]

aenv =
    inserts
        [ (Idt "{-}", ari $ ariOp (-)),
          (Idt "{*}", ari $ ariOp (*)),
          (Idt "{+}", ari $ ariOp (+)),
          (Idt "{/}", ari $ AriOp (\x y -> if y /= 0 then Just $ x `div` y else Nothing)),
          (Idt "{>}", ari $ ariOp (\x y -> if x > y then 1 else 0)),
          (Idt "{<}", ari $ ariOp (\x y -> if x < y then 1 else 0)),
          (Idt "{>=}", ari $ ariOp (\x y -> if x >= y then 1 else 0)),
          (Idt "{<=}", ari $ ariOp (\x y -> if x <= y then 1 else 0)),
          (Idt "{==}", ari $ ariOp (\x y -> if x == y then 1 else 0))
        ]
        Map.empty

atenv =
    inserts
        [ (Idt "{-}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
          (Idt "{*}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
          (Idt "{+}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
          (Idt "{/}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
          (Idt "{>}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
          (Idt "{<}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
          (Idt "{>=}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
          (Idt "{<=}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
          (Idt "{==}", Scheme [] $ TFunc TInt (TFunc TInt TInt))
        ]
        Map.empty

cc x = runReaderT (calc x) aenv
bb x fname = runReaderT (bind x) (Map.insert (Idt fname) (EBVar $ Idt fname) aenv)

getInts :: Map.Map Idt (Either String ExpBound) -> [(Idt, [Integer])]
getInts m = [(k, h : t) | (k, Just (h : t)) <- Map.toList $ Map.map f m]
  where
    f (Right (EBOverload [])) = return []
    f (Right (EBOverload ((EBInt x) : xs))) = fmap (x :) $ f (Right $ EBOverload xs)
    f (Right (EBOverload (x : xs))) = f (Right $ EBOverload xs)
    f (Right (EBInt x)) = return [x]
    f _ = Nothing

type FullEnv = (BEnv, Map.Map Idt Scheme, VariantEnv, Map.Map Idt (Idt, Integer, Integer))
emptyEnvs :: FullEnv
emptyEnvs = (aenv, atenv, emptyEnv, Map.fromList bop)

processDecl :: FullEnv -> Decl -> Except String FullEnv
processDecl (env, tenv, venv, ops) (DExp name tds exp) = do
    unboundUnchecked <- fmap (\infd -> ELet name tds infd (EVar name)) $ infixate exp ops
    unbound <- bindZeroargMatches unboundUnchecked (venv, tenv)
    if is_typed tds
        then
            let bound = bindRecurrent unbound name env
                current = case Map.lookup name tenv of
                    Just (Scheme vars t) -> t
                    Nothing -> TOverload []
             in do
                    (boundType, exps) <- fmap overloadify $ overloadInference tenv venv bound name
                    calcedExp <- runReaderT (calc exps) env
                    let bounds = expToList calcedExp
                     in case Map.lookup name env of
                            Just (EBOverload xs) ->
                                return
                                    ( Map.insert name (EBOverload $ xs ++ bounds) env,
                                      Map.insert name (generalize (TypeEnv tenv) (sumTypes current boundType)) tenv,
                                      venv,
                                      ops
                                    )
                            _ ->
                                return
                                    ( Map.insert name (EBOverload bounds) env,
                                      Map.insert name (generalize (TypeEnv tenv) boundType) tenv,
                                      venv,
                                      ops
                                    )
        else
            let bound = bindRecurrent unbound name env
             in do
                    (typeAssignment, exps) <- overloadInference tenv venv bound name
                    calcedExp <- runReaderT (calc exps) env
                    return
                        ( Map.insert name calcedExp env,
                          Map.insert name (generalize (TypeEnv tenv) typeAssignment) tenv,
                          venv,
                          ops
                        )
processDecl envs (DType name tvs []) = return envs
processDecl (env, tenv, venv, ops) (DType name tvs ((VarType vname ts) : t)) =
    if all (flip elem tvs) (Set.elems $ ftv $ TVariant vname ts)
        then
            processDecl
                ( let tng [] n = []
                      tng (h : t) n = (Idt $ "a" ++ show n) : tng t (n + 1)
                      foldFuncs [] acc = acc
                      foldFuncs (h : t) acc = TFunc h (foldFuncs t acc)
                      tns = tng ts 0
                   in ( Map.insert vname (EBLam Map.empty tns (EBVariant vname (map EBVar tns))) env,
                        Map.insert vname (Scheme tvs $ foldFuncs ts $ TVariant name (map TVar tvs)) tenv,
                        insertCons vname (Scheme tvs $ TVariant name (map TVar tvs)) venv,
                        ops
                      )
                )
                (DType name tvs t)
        else throwError "Unbound type variable in type definition"
processDecl (env, tenv, venv, ops) (DLOp prec op sem) = return (env, tenv, venv, Map.insert op (sem, prec, -1) ops)
processDecl (env, tenv, venv, ops) (DROp prec op sem) = return (env, tenv, venv, Map.insert op (sem, prec, 1) ops)

str_to_calc :: String -> Except String String
str_to_calc x = case pProgram (myLexer x) of
    Left err -> throwError err
    Right (Prog es) ->
        let envs = foldM processDecl emptyEnvs es
         in do
                (env, tenv, venv, ops) <- envs
                return $
                    (show tenv)
                        ++ "\n\n===============\n\n"
                        ++ (show env)
                        ++ "\n\n========================\n\n"
                        ++ (show venv)
                        ++ "\n\n========================\n\n"
                        ++ (show $ Map.map (\x -> runExcept (runReaderT (calc x) env)) env)
                        ++ "\n\n========================\n\n"
                        ++ (show $ getInts $ Map.map (\x -> runExcept (runReaderT (calc x) env)) env)
      where

ppConses :: [(Idt, Scheme)] -> String
ppConses [] = ""
ppConses ((name, scheme) : t) =
    show name ++ " of " ++ show scheme ++ "\n" ++ ppConses t

processDeclIO :: FullEnv -> Decl -> ExceptT String IO FullEnv
processDeclIO envs x =
    let declEnvs = processDecl envs x
     in case runExcept declEnvs of
            Left err -> throwError err
            Right res@(env, tenv, venv, ops) -> case x of
                DExp name _ _ -> do
                    lift $ putStrLn $ show name ++ " of " ++ (show $ fromJust $ Map.lookup name tenv) ++ " is "
                    lift $ putStrLn $ show $ fromJust $ Map.lookup name env
                    return res
                DType name _ _ -> do
                    lift $ putStrLn $ ppConses $ map (\x -> (x, fromJust $ Map.lookup x tenv)) $ getConses name venv
                    return res
                DLOp prec op sem -> do
                    lift $ putStrLn $ "Left-binding operator " ++ show op ++ " with precedence " ++ show prec ++ " is " ++ show sem
                    return res
                DROp prec op sem -> do
                    lift $ putStrLn $ "Right-binding operator " ++ show op ++ " with precedence " ++ show prec ++ " is " ++ show sem
                    return res

runProgram :: FullEnv -> String -> ExceptT String IO FullEnv
runProgram envs x = case pProgram (myLexer x) of
    Left err -> throwError err
    Right (Prog es) -> foldM processDeclIO envs es

doesExprEnd :: String -> Bool
doesExprEnd ";;" = True
doesExprEnd (x : y : xs) = doesExprEnd (y : xs)
doesExprEnd _ = False

main :: IO ()
main = do
    args <- getArgs
    case args of
        [fname] -> do
            file <- readFile fname
            case runExcept $ str_to_calc file of
                Left err -> hPutStrLn stderr err
                Right res -> putStrLn res
        _ -> do
            putStrLn "Welcome to Paweł!"
            putStrLn "Type :q to quit"
            let mainloop envs = do
                    putStr "Paweł> "
                    let inputloop = do
                            hFlush stdout
                            line <- getLine
                            if line == ":q"
                                then return Nothing
                                else
                                    if doesExprEnd line
                                        then return $ Just line
                                        else do
                                            rest <- inputloop
                                            case rest of
                                                Nothing -> return Nothing
                                                Just rest' -> return $ Just $ line ++ "\n" ++ rest'
                     in do
                            unparsed <- inputloop
                            case unparsed of
                                Nothing -> putStrLn "Quitting..."
                                Just unparsed' -> do
                                    result <- runExceptT $ runProgram envs unparsed'
                                    case result of
                                        Left err -> do hPutStrLn stderr err; mainloop envs
                                        Right res -> mainloop res
             in mainloop emptyEnvs

