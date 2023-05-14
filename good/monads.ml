-- użycie: ./interpreter good/regularAri.ml good/Prelude.ml good/monads.ml
-- lub ./interpreter good/overloadAri.ml good/Prelude.ml good/monads.ml

op left 1 >>= = {>>=};;
op left 1 >> = {>>};;

-- Monady to zastosowanie, w którym klasy typów błyszczą wydajnościowo,
-- natomiast przeładowania są dydaktycznie ciekawsze:
-- zawsze liczone są wszystkie możliwe warianty,
-- czyli dopóki obliczenia są abstrakcyjne, to możemy obserwować,
-- jak wyglądałby wynik w zależności od tego, jakiej monady używamy.
-- Na przykład return 5 dostaje typ 
-- Forall a15,a16,a17. overload(List(Int),
--                              Maybe(Int),
--                              Either(a15,Int),
--                              State(a15,Int),
--                              Reader(a15,Int),
--                              TCM(a15,a16,a17,Int))
-- Oznacza to niestety, że jeśli w kodzie funkcji jest wiele obliczeń
-- monadycznych, to będzie się ona typowała bardzo powoli.

let {>>=} (a:List of a) (f:b -> List of b) = flatten (map f a);;
let return (a:a) = [a, ];;

type Maybe of a = Just a | Nothing;;
let {>>=} (a:Maybe of a) (f:a->Maybe of b) = match a with
    Nothing => Nothing
    | Just a => f a;;
let return (a:a) = Just a;;

type Either of a b = Left a | Right b;;
let {>>=} (a:Either of a b) (f:b -> Either of a c) = match a with
    Left l => Left l
    | Right r => f r;;
let return (a:a) = Right a;;

type State of state result = State (state -> Pair of result state);;
let runState a b = match a with
    State f => f b;;
let {>>=} (a:State of a b) (f:b -> State of a c) = match a with
    State f' => State (λs.
        let pair = f' s in match pair with
            a ,, s' => runState (f a) s'
    );;
let return (a:a) = State (λs . a,, s);;
let get = State (λs. s,, s);;
let put s = State (λ_ . (Nothing,, s));;
let modify f = get >>= (λx.put (f x));;
let execState f = snd o runState f;; -- tutaj o jest złożeniem, funkcja z Prelude.ml
let evalState f = fst o runState f;;

type Reader of env result = Reader (env -> result);;
let reader = Reader;;
let runReader a b = match a with
    Reader f => f b;;
let {>>=} (a:Reader of a b) (f:b -> Reader of a c) = match a with
    Reader f' => Reader $ λ env. runReader (f (f' env)) env;;
let return (a:a) = Reader (λ_ . a);;
let ask = Reader id;;
let local f a = match a with
    Reader f' => Reader $ λ env. f' (f env);;

-- Nie możemy zdefiniować transformatorów monad jak w Haskellu,
-- bo wtedy mielibyśmy nieskończenie wiele monad,
-- a Paweł nas chroni przed nieskończonymi przeładowaniami.
-- Musimy więc TypeCheckingMonad zdefiniować na Piechotę.
type TCM of error state env result = TCM (state -> env -> Pair of (Either of error result) state);;
let runTCM tcm state env = match tcm with
    TCM f => f state env;;
let {>>=} (a:TCM of er s en r) (f:r -> TCM of er s en r') = match a with
    TCM f' => TCM (λs env.
        let pair = f' s env in match pair with
            (Right res) ,, s' => runTCM (f res) s' env
            | (Left err) ,, s' => Left err ,, s'
    );;
let return (a:a) = TCM (λs e. (Right a) ,, s);;

-- Każda monada ma osobno nazwane operacje monadyczne,
-- w szczególności get i ask nie da się przeładować.
let getTCM = TCM (λ s env. (Right s) ,, s);;
let askTCM = TCM (λ s env. (Right env) ,, s);;
let localTCM f a = match a with
    TCM f' => TCM $ λ s env. f' s (f env);;
let putTCM s = TCM (λ _ env. (Right Nothing) ,, s);;
let modifyTCM f = getTCM >>= (λx.putTCM (f x));;


-- Mamy zdefiniowane kilka monad, więc możemy podefiniować
-- operacje monadyczne na nich.

let mapM (f : a -> m) (l : List of a) = match l with
    Empty => return Empty
    | h,t => (f h) >>= (λfh. mapM f t >>= (λft. return $ fh, ft));;
let foldM (f : b -> a -> m) (acc : b) (l : List of a) = match l with
    Empty => return acc
    | h,t => (f acc h) >>= (λfah. foldM f fah t);;

let {>>} a b = {>>=} a (λ_  . b);;
let fmap f m = m >>= (return o f);;
let pure = return;;

op left 4 <*> = {<*>};;
let {<*>} mfab ma = mfab >>= (λfab. ma >>= (return o fab));;