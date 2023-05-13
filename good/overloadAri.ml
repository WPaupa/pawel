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