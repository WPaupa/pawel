-- użycie: ./interpreter good/overloadAri.ml good/Prelude.ml good/Data.ml

-- Aplikacja intów w Pawle bardzo naturalnie wynika
-- z rekurencji pierwotnej.

-- Tutaj działamy jakbyśmy robili pętlę od 1 do 10 i dla każdej
-- wartości iteratora sprawdzamy, czy iterator razy dzielnik to dzielna.
-- Jeśli tak, to ustawiamy flagę na 1 i kontynuujemy. Jeśli nie,
-- to flagi nie zmieniamy.
let divides x y = fst $ y (λk. if (fst k == 1) || (snd k * x == y) then (1,,snd k+1) else (0,,snd k+1)) (0,,1);;

-- Jednakże nie tylko funkcje pierwotnie rekurencyjne
-- są wyrażalne w Pawle za pomocą aplikacji.

let ackermann m = m (λA. (λn. ({+} n 1) A 1)) (id + 1);;

-- To naprowadza nas na wniosek, że w Pawle bez rekurencji (!)
-- wyrażalne są wszystkie funkcje dowodliwie obliczalne
-- w arytmetyce Peano.