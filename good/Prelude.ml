op right 0 $  = {$};;
op right 2 || = {||};;
op right 3 && = {&&};;
op right 4 == = [==];;
op right 4 /= = [/=];;
op right 4 <  = [<];;
op right 4 >  = [>];;
op right 4 <= = [<=];;
op right 4 >= = [>=];;
op left  6 +  = [+];;
op left  6 -  = [-];;
op left  7 /  = [/];;
op left  7 *  = [*];;
op left  7 mod = modulo;;
op right 8 ** = [**];;
op right 9 o  = {o};;
op left  9 !! = {!!};; 

op right 5 ,  = Cons;;
op right 5 :: = Cons;;
op right 5 ++ = {++};;
op right 5 has = elem;;

let id x = x;;
let {$} f x = f x;;
let {o} f g x = f (g x);;
let const x y = x;;
let flip f x y = f y x;;
let undefined x = undefined x;; 
-- zaaplikowanie undefined do dowolnego wyrazu zawiesza program,
-- ale samo undefined nie jest jeszcze wyliczone

let int (x:Int) = x;; -- funkcja ukonkretniająca 

-- Redefiniujemy operatory bazowe w przeładowany sposób.
let [+]  (a:Int) (b:Int) = {+} a b;;
let [-]  (a:Int) (b:Int) = {-} a b;;
let [*]  (a:Int) (b:Int) = {*} a b;;
let [/]  (a:Int) (b:Int) = {/} a b;;
let [==] (a:Int) (b:Int) = {==} a b;;
let [<]  (a:Int) (b:Int) = {<} a b;;
let [>]  (a:Int) (b:Int) = {>} a b;;
let [<=] (a:Int) (b:Int) = {<=} a b;;
let [>=] (a:Int) (b:Int) = {>=} a b;;

-- Oraz na przykład coś własnego
let [**] (a:Int) (b:Int) = b ({*} a) 1;;
let [/=] a b = {-} 1 ({==} a b);;

-- Teraz możemy je zdefiniować dla innych typów
-- Konwencja: operatory przeładowane dla funkcji
-- oznaczamy w nawiasach kwadratowych, a bazowe - w klamrowych
let [+]  (a:a->b) (b:a->b) x = {+} (a x) (b x);;
let [-]  (a:a->b) (b:a->b) x = {-} (a x) (b x);;
let [*]  (a:a->b) (b:a->b) x = {*} (a x) (b x);;
let [/]  (a:a->b) (b:a->b) x = {/} (a x) (b x);;
let [==] (a:a->b) (b:a->b) x = {==} (a x) (b x);;
let [<]  (a:a->b) (b:a->b) x = {<} (a x) (b x);;
let [>]  (a:a->b) (b:a->b) x = {>} (a x) (b x);;
let [<=] (a:a->b) (b:a->b) x = {<=} (a x) (b x);;
let [>=] (a:a->b) (b:a->b) x = {>=} (a x) (b x);;

let [**] (a:a->b) (b:a->b) x = (b x) ({*} (a x)) 1;;
let [/=] (a:a->b) (b:a->b) x = {-} 1 ({==} (a x) (b x));;


let [+]  (a:a->b) b x = {+} (a x) b;;
let [-]  (a:a->b) b x = {-} (a x) b;;
let [*]  (a:a->b) b x = {*} (a x) b;;
let [/]  (a:a->b) b x = {/} (a x) b;;
let [==] (a:a->b) b x = {==} (a x) b;;
let [<]  (a:a->b) b x = {<} (a x) b;;
let [>]  (a:a->b) b x = {>} (a x) b;;
let [<=] (a:a->b) b x = {<=} (a x) b;;
let [>=] (a:a->b) b x = {>=} (a x) b;;

let [**] (a:a->b) b x = b ({*} (a x)) 1;;
let [/=] (a:a->b) b x = {-} 1 ({==} (a x) b);;


let [+]  a (b:a->b) x = {+} a (b x);;
let [-]  a (b:a->b) x = {-} a (b x);;
let [*]  a (b:a->b) x = {*} a (b x);;
let [/]  a (b:a->b) x = {/} a (b x);;
let [==] a (b:a->b) x = {==} a (b x);;
let [<]  a (b:a->b) x = {<} a (b x);;
let [>]  a (b:a->b) x = {>} a (b x);;
let [<=] a (b:a->b) x = {<=} a (b x);;
let [>=] a (b:a->b) x = {>=} a (b x);;

let [**] a (b:a->b) x = (b x) ({*} a) 1;;
let [/=] a (b:a->b) x = {-} 1 ({==} a (b x));;

-- Na ich podstawie możemy zdefiniować nowe operatory, bazowo przeładowane,
-- ale bez szybkiego ukonkretnienia często będą mnożyć się dostępne przeładowania
let modulo a b = a - (b * (a / b));;

-- Warto mieć też modulo tylko dla intów
let {mod} a b = {-} a ({*} b ({/} a b));;

-- Operatory logiczne, dla intów troszczymy się, żeby nie wybuchło 
let ifnzero a = if a then 1 else 0;; 
let ifzero a = if a then 0 else 1;;
let {&&} (a:Int) (b:Int) = int $ (ifnzero a) * (ifnzero b);;
let {||} (a:Int) (b:Int) = ifnzero $ (ifnzero a) + (ifnzero b);;

-- Pary
type Pair of a b = Pair a b;;
op right 5 ,, = Pair;;
let fst x = match x with (a ,, b) => a;;
let snd x = match x with (a ,, b) => b;;
let foldp f x = match x with (a ,, b) => f a b;;
let pairFunctions f g x = f x ,, g x;;

-- Wartości Boolowskie
type Bool of = False | True;;
-- Pisanie "Bool of" jest trochę brzydkie, ale spełnia ważną funkcję:
-- pozwala odróżnić zmienną typową od konstruktora typu 
-- np x:(Bool of) -> Int jest funkcją z boola do inta, a x:Bool->Int jest
-- funkcją z dowolnego typu (oznaczonego przez Bool) do inta
let [&&] (a:Bool of) (b:Bool of) = let q = a ,, b in match q with
    True ,, True => True
    | _ => False;;
let [||] (a:Bool of) (b:Bool of) = let q = a ,, b in match q with
    False ,, False => False
    | _ => True;;
let not (a:Bool of) = match a with
    False => True
    | True => False;;
let int (a:Bool of) = match a with
    False => 0
    | True => 1;;

-- Operacje na listach
type List of a = Empty | Cons a (List of a);;

let head default list = match list with 
    Empty => default 
    | Cons a b => a;;
let tail list = match list with 
    Empty => Empty 
    | Cons a b => b;;

let foldRight f acc list = match list with 
    Empty => acc 
    | Cons a b => f (foldRight f acc b) a;;
let foldLeft  f acc list = match list with 
    Empty => acc 
    | Cons a b => foldLeft f (f acc a) b;;
let map f list = match list with 
    Empty => Empty 
    | Cons a b => Cons (f a) (map f b);;
let filter pred list = match list with
    Empty => Empty
    | Cons a b => if pred a then Cons a (filter pred b) else filter pred b;;

-- Listy można matchować także operatorem ,
let {++} l m = match l with Empty => m | h, t => h, (t ++ m);;
let flatten list = match list with
    Empty => Empty
    | h,t => h ++ flatten t;;
let {!!} list n = match list with 
    h, t => if ifzero n then h else {!!} t ({-} n 1);;

-- Pełen (chociaż trochę dziwny) lukier syntaktyczny dla list można zdefiniować w języku
let [ x = x;;
let ] = Empty;;
-- Dzięki temu można na przykład tworzyć listy typu [1,2,3, ] 
-- (nie można zapominać o przecinku i spacji na końcu, żeby ,] nie zostało potraktowane jako osobny operator)
-- Sprawia to też, że listy nie mają odgórnej precedencji, tylko parsują się zgodnie z precedencją operatorów.
-- Z tego powodu na przykład [1, 2, 3, ] !! 2 sparsuje się jako 1, 2, 3, (Empty !! 2) o poprawnym typie i błędzie matcha
-- Należy więc w takich sytuacjach używać nawiasów.

-- Ta definicja stworzy kopie procedury elem dla każdego typu elementów listy, którego
-- przeładowanie porównania zwraca inta (coś, co może być pod ifem). Dlatego musi być
-- napisana po definicjach równości dla typów.
let elem list q = match list with 
    Empty => 0 
    | h, t => if h == q then 1 else elem t q;;