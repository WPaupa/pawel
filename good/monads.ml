op left 1 >>= = {>>=};;
op left 1 >> = {>>};;

-- Monady to zastosowanie, w którym klasy typów błyszczą wydajnościowo,
-- natomiast przeładowania są dydaktycznie ciekawsze:
-- zawsze liczone są wszystkie możliwe warianty,
-- czyli dopóki obliczenia są abstrakcyjne, to możemy obserwować,
-- jak wyglądałby wynik w zależności od tego, jakiej monady używamy.
-- Na przykład return 5 dostaje typ 
-- Forall a10. overload(State(a10,Int),
--                   Reader(a10,Int),
--                   Maybe(Int),
--                   Either(a10,Int),
--                   List(Int))

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
let {>>=} (a:State of a b) (f:b -> State of a b) = match a with
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
let {>>=} (a:Reader of a b) (f:b -> Reader of a b) = match a with
    Reader f' => Reader $ λ env. runReader (f (f' env)) env;;
let return (a:a) = Reader (λ_ . a);;
let ask = Reader id;;
let local f a = match a with
    Reader f' => Reader $ λ env. f' (f env);;

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