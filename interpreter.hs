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
import System.Exit

is_typed :: [TypeDecl] -> Bool
is_typed [] = False
is_typed ((TDVar _) : t) = is_typed t
is_typed ((TDType _ _) : t) = True

expToList :: ExpBound -> [ExpBound]
expToList (EBOverload xs) = xs
expToList x = [x]

-- Środowiska operatorów, stałych i typów
-- na początku wykonania programu.
bop = []

aenv = Map.fromList
    [   (Idt "{-}", ari $ ariOp (-)),
        (Idt "{*}", ari $ ariOp (*)),
        (Idt "{+}", ari $ ariOp (+)),
        (Idt "{/}", ari $ AriOp (\x y -> if y /= 0 then Just $ x `div` y else Nothing)),
        (Idt "{>}", ari $ ariOp (\x y -> if x > y then 1 else 0)),
        (Idt "{<}", ari $ ariOp (\x y -> if x < y then 1 else 0)),
        (Idt "{>=}", ari $ ariOp (\x y -> if x >= y then 1 else 0)),
        (Idt "{<=}", ari $ ariOp (\x y -> if x <= y then 1 else 0)),
        (Idt "{==}", ari $ ariOp (\x y -> if x == y then 1 else 0))
    ]

atenv = Map.fromList
    [   (Idt "{-}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
        (Idt "{*}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
        (Idt "{+}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
        (Idt "{/}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
        (Idt "{>}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
        (Idt "{<}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
        (Idt "{>=}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
        (Idt "{<=}", Scheme [] $ TFunc TInt (TFunc TInt TInt)),
        (Idt "{==}", Scheme [] $ TFunc TInt (TFunc TInt TInt))
    ]

-- Typ dla sumy wszystkich środowisk potrzebnych do wykonania programu.
-- Są to po kolei środowisko wyrażeń, środowisko przypisań typowych,
-- środowisko samych typów i środowisko operatorów. 
type FullEnv = (BEnv, Map.Map Idt Scheme, VariantEnv, Map.Map Idt (Idt, Integer, Integer))
emptyEnvs :: FullEnv
emptyEnvs = (aenv, atenv, emptyEnv, Map.fromList bop)

-- Funkcja licząca środowisko po wykonaniu deklaracji.
-- Dla wyrażeń: najpierw infiksujemy operatory, zamieniamy
-- strukturę wyrażenia na coś postaci let exp = ... in exp,
-- zmieniamy konstruktory jednoargumentowe na MCons [] (parser
-- przypisał im strukturę MVar), a potem jeśli jakiś argument jest
-- otypowany, to dodajemy wyrażenie do możliwych overloadów,
-- a jeśli nie, to przysłaniamy nim poprzednie definicje.
-- Dalej: najpierw bindujemy przeładowane zmienne, potem
-- nadajemy im typy, a potem liczymy wyrażenia. Musimy się
-- troszczyć o to, żeby lista przeładowań typów odpowiadała jednoznacznie
-- liście przeładowań wyrażeń.  
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
-- Dla deklaracji typów: najpierw sprawdzamy, czy wszystkie zmienne
-- są związane, a potem konstruujemy typy dla konstruktorów
-- i dodajemy do środowiska funkcji oraz przypisań typowych, a do środowiska typów
-- dodajemy przetwarzany typ.
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
processDecl (env, tenv, venv, ops) (DLOp prec op sem) = return (env, tenv, venv, Map.insert op (sem, prec, 1) ops)
processDecl (env, tenv, venv, ops) (DROp prec op sem) = return (env, tenv, venv, Map.insert op (sem, prec, -1) ops)

ppConses :: [(Idt, Scheme)] -> String
ppConses [] = ""
ppConses ((name, scheme) : t) =
    show name ++ " of " ++ show scheme ++ "\n" ++ ppConses t

-- Funkcja przetwarza deklarację oraz wypisuje komunikat dla użytkownika. 
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

-- Jeśli program wywołamy z argumentami, to wczytujemy pliki
-- podane w argumentach i wykonujemy je po kolei. Plikiem
-- może być też stdin. Jeśli nie podamy argumentów, to
-- uruchamiamy toplevel. Błąd w pliku skutkuje przerwaniem
-- wykonania programu, błąd w toplevelu tylko komunikatem.
main :: IO ()
main = 
    let mainloop envs = do
            putStr "Paweł> "
            let inputloop = do
                    hFlush stdout
                    line <- getLine
                    if line == ":q"
                        then return Nothing
                    else if doesExprEnd line
                        then return $ Just line
                    else do
                        rest <- inputloop
                        case rest of
                            Nothing -> return Nothing
                            Just rest' -> return $ Just $ line ++ "\n" ++ rest'
                in do
                unparsed <- inputloop
                case unparsed of
                    Nothing -> return envs
                    Just unparsed' -> do
                        result <- runExceptT $ runProgram envs unparsed'
                        case result of
                            Left err -> do hPutStrLn stderr err; mainloop envs
                            Right res -> mainloop res
     in do
        args <- getArgs
        case args of
            [] -> do
                putStrLn "Welcome to Paweł!"
                putStrLn "Type :q to quit"
                _ <- mainloop emptyEnvs
                putStrLn "Quitting...";
            _ ->
                let process envs fname = do
                        file <- readFile fname
                        result <- runExceptT $ runProgram envs file
                        case result of
                            Left err -> do hPutStrLn stderr $ err ++ "\nErrors in file, exiting..."; exitWith $ ExitFailure 1
                            Right envs' -> return envs' 
                in foldM_ (\envs fname -> if fname == "stdin" then mainloop envs else process envs fname) emptyEnvs args

