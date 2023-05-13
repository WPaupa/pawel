-- Ten sposób implementowania łańcuchów znaków
-- jest bardzo daleki perfekcji,
-- ale w języku bez wejścia i wyjścia
-- oraz semantycznego wsparcia dla napisów
-- i tak trudno liczyć na cokolwiek lepszego.

let '0' = 48;;
let '1' = 49;;
let '2' = 50;;
let '3' = 51;;
let '4' = 52;;
let '5' = 53;;
let '6' = 54;;
let '7' = 55;;
let '8' = 56;;
let '9' = 57;;
let ':' = 58;;
let '<' = 60;;
let '=' = 61;;
let '>' = 62;;
let '?' = 63;;
let 'A' = 65;;
let 'B' = 66;;
let 'C' = 67;;
let 'D' = 68;;
let 'E' = 69;;
let 'F' = 70;;
let 'G' = 71;;
let 'H' = 72;;
let 'I' = 73;;
let 'J' = 74;;
let 'K' = 75;;
let 'L' = 76;;
let 'M' = 77;;
let 'N' = 78;;
let 'O' = 79;;
let 'P' = 80;;
let 'Q' = 81;;
let 'R' = 82;;
let 'S' = 83;;
let 'T' = 84;;
let 'U' = 85;;
let 'V' = 86;;
let 'W' = 87;;
let 'X' = 88;;
let 'Y' = 89;;
let 'Z' = 90;;
let '[' = 91;;
let ']' = 93;;
let '_' = 95;;
let 'a' = 97;;
let 'b' = 98;;
let 'c' = 99;;
let 'd' = 100;;
let 'e' = 101;;
let 'f' = 102;;
let 'g' = 103;;
let 'h' = 104;;
let 'i' = 105;;
let 'j' = 106;;
let 'k' = 107;;
let 'l' = 108;;
let 'm' = 109;;
let 'n' = 110;;
let 'o' = 111;;
let 'p' = 112;;
let 'q' = 113;;
let 'r' = 114;;
let 's' = 115;;
let 't' = 116;;
let 'u' = 117;;
let 'v' = 118;;
let 'w' = 119;;
let 'x' = 120;;
let 'y' = 121;;
let 'z' = 122;;

-- W razie gdyby nie była zaimportowana biblioteka overloadAri
op right 4 == = [==];;
op right 4 /= = [/=];;
op right 4 <  = [<];;
op right 4 >  = [>];;
op right 4 <= = [<=];;
op right 4 >= = [>=];;
let [==] (a:Int) (b:Int) = {==} a b;;
let [<]  (a:Int) (b:Int) = {<} a b;;
let [>]  (a:Int) (b:Int) = {>} a b;;
let [<=] (a:Int) (b:Int) = {<=} a b;;
let [>=] (a:Int) (b:Int) = {>=} a b;;

let [==] (a:List of Int) (b:List of Int) = let k = a ,, b in match k with
    Empty ,, Empty => 1
    | (h1,t1) ,, (h2,t2) => ({==} h1 h2) && ([==] t1 t2)
    | _ => 0;;

let [/=] (a:List of Int) (b:List of Int) = 1 - (a == b);;

let [<] (a:List of Int) (b:List of Int) = let k = a ,, b in match k with
    (h1,t1) ,, (h2,t2) => ({<} h1 h2) || (({==} h1 h2) && ([<] t1 t2))
    | Empty ,, (h2,t2) => 1
    | _ => 0;;

-- Niekoniecznie optymalne, ale za to ładne
let [<=] (a:List of Int) (b:List of Int) = (a == b) || (a < b);;
let [>]  (a:List of Int) (b:List of Int) = 1 - (a <= b);;
let [>=] (a:List of Int) (b:List of Int) = (a == b) || (a > b);;

let show (x:Int) = 
    let showRev (x:Int) = 
        if {==} ({/} x 10) 0 then [ ({+} x 48), ]
        else ({+} 48 ({mod} x 10)) , (showRev $ {/} x 10) in
    reverse $ showRev x;;
let show (x:List of Int) = x;;