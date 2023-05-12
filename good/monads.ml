op left 1 >>= = {>>=};;
op left 1 >> = {>>};;

-- Monady to zastosowanie, w którym klasy typów błyszczą wydajnościowo,
-- natomiast przeładowania są dydaktycznie ciekawsze:
-- zawsze liczone są wszystkie możliwe warianty,
-- czyli dopóki obliczenia są abstrakcyjne, to możemy obserwować,
-- jak wyglądałby wynik w zależności od tego, jakiej monady używamy.
-- Na przykład return 5 dostaje typ 

type Maybe of a = Just a | Nothing;;
type Either of a b = Left a | Right b;;
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

let {>>=} (a:Maybe of a) (f:a->Maybe of b) = match a with
    Nothing => Nothing
    | Just a => f a;;
let return (a:a) = Just a;;

let {>>=} (a:Either of a b) (f:b -> Either of a c) = match a with
    Left l => Left l
    | Right r => f r;;
let return (a:a) = Right a;;

-- Mamy zdefiniowane kilka monad, więc możemy podefiniować
-- operacje monadyczne na nich.

let mapM (f : a -> m) (l : List of a) = match l with
    Empty => return Empty
    | h,t => (f h) >>= (λfh. mapM f t >>= (λft. return $ fh, ft));;
let foldM (f : b -> a -> m) (acc : b) (l : List of a) = match l with
    Empty => return acc
    | h,t => (f acc h) >>= (λfah. foldM f fah t);;

let {>>} a b = {>>=} a (λ_  . b);;