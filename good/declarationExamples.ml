-- Przykłady z deklaracji języka

let K x y = x;;

let f (x : Int) y = x + 1;;
let f (x : (Int -> Int)) y = y;;
let g y = f (λx. y);;

let h (x : Int) (y : Bool of) = x;;
let h (x : Bool of) (y : Int) = y;;
let h (x : Int) (y : Int) = x;;
let h (x : Bool of) (y : Bool of) = 0;;
let i x y z = h (h x y) z;;

let piecewiseAdd (x : Int) (y : Int) = x + y;;
let piecewiseAdd (x : List of Int) (y : List of Int) = let z = x ,, y in 
    match z with
        (h1, t1) ,, (h2, t2) => (int $ h1 + h2) , (piecewiseAdd t1 t2)
        | _ => Empty;;

let dziesiec = int $ (λx.x * 2) 5;;
let trzydziesci_dwa = int $ 5 (λx. x * 2) 1;;

let power1 n m = if m then n * (power1 n (m - 1)) else 1;;
let power2 n m = (int m) ({*} n) 1;;
let power3 n m = m (id * n) 1;;
let power4 n m = m n;;

let factorial n = snd $ n (pairFunctions (fst + 1) (foldp {*})) (1 ,, 1);;
