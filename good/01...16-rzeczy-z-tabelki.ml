-- użycie: ./Conn good/regularAri.ml good/Prelude.ml good/01...16-rzeczy-z-tabelki.ml
-- Polecam co do zasady odpalać Pawła za pomocą ledit ./Conn [pliki] stdin

-- Przykłady na każdy z punktów z tabelki.
-- Punkty, które są demonstrowane tym, że coś się nie kompiluje,
-- zawarto w wykomentowanych linijkach.

-- 1. Dwa typy wyrażeń (w Pawle if int ma poprawny typ, ale if bool - już niepoprawny)
-- W przyszłej wersji Pawła if bool też będzie miało poprawny typ (dzięki przeładowaniom).

let k = if 1 then 1 else 0;;
-- let k = if True then 1 else 0;;

-- 2. Arytmetyka, porównania
let k = if 1 + 2 * 3 < (1 + 2) * 3 then 2 ** 1 ** 3 else (2 ** 1) ** 3;;
let k = if 1 == 2 then False else True;;

-- 3. Wyrażenie if 
let k = if 1 then if 1 then if 1 then True else False else False else False;;

-- 4. Funkcje wieloargumentowe, rekurencja
let max x y = if x < y then y else x;;
let min x y = if x < y then x else y;;
let NWD x y = if x then if y then NWD (max x y - min x y) (min x y) else x else y;; 

let h = NWD 1000 255;;

-- 5. Funkcje anonimowe, częściowa aplikacja, funkcje wyższego rzędu, domknięcia
let a q = let u = λx. q x in u;;
let k = a (λx. x + 1);;

-- 6. Obsługa błędów wykonania, np. dzielenie przez zero 
-- let u = 1 / 0;;
-- let u = let x = False in match x with True => True;;

-- 7. Statyczne wiązanie identyfikatorów
let a = 5;;
let u x = a;;
let a = 3;;
let h = u 0;;

-- Listy z:
-- 8. Pattern matchingiem [] | x:xs
let k x = match x with
    Empty => 0
    | h , t => h;;
let h = k (Cons 1 Empty);;

-- (9. lub zestawem wbudowanych operacji empty, head, tail: 
-- w Pawle tego nie ma, operacje empty, head i tail nie są wbudowane)
let k = head (tail (Cons 1 (Cons 2 Empty)));;

-- 10. Mile widziany lukier syntaktyczny do wpisywania stałych list
let k = [1, 2, 3, ];;

-- 11. Listy dowolnego typu, także listy zagnieżdżone i listy funkcji
let k = [(λx.x), (λx.x + 1), ];;
let k = [([1, 2, 3, ]), ([4, 5, 6, ]), ];;
let u = flatten k;;

-- 12. lub ogólne rekurencyjne typy algebraiczne z pattern matchingiem
-- (w Pawle jest i jedno i drugie)
type k of = v1 Int Int | v2;;
let h k = match k with v1 a b => a | v2 => 0;;
let k = h v2 + h (v1 5 0);;

-- 13. Statyczne typowanie. Na tym poziomie można wymagać jawnego podawania typów
let y (x:Int) = x;;
-- let h = y True;;

-- 14. Ogólne polimorficzne i rekurencyjne typy algebraiczne.
type recc of a = In ((recc of a) -> a);;
let out f = match f with In x => x;;
let Y f = (λx a. f (out x x) a) (In (λx a. f (out x x) a));;
-- Mamy kombinator punktu stałego w Pawle!

-- 15. Dowolne zagnieżdżenie wzorców w pattern matchingu
let fifth list = match list with 
    h1, (h2, (h3, (h4, (h5, t)))) => h5;;
let k = fifth ([1, 2, 3, 4, 5, 6, 7, 8, ]);;

-- 16. Typy polimorficzne w stylu ML z algorytmem rekonstrukcji typów.
-- let Y f = (λx. f (x x))(λx. f (x x));; -- normalnie kombinator Y się nie typuje