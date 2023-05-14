-- W języku Paweł operator - jest ściśle operatorem binarnym.
-- Oznacza to, że ten zapis nie sparsuje się poprawnie do -1. 
let k = -1;;

-- Stała [] jest zdefiniowana w języku, więc można ją przysłaniać.
-- Z tego powodu wyrażenie:
let h (l:List of a) = match l with
    [] => 1
    | h, t => 0;;
-- nigdy nie wejdzie do drugiej gałęzi, bo [] zostanie potraktowane
-- jako match postaci pojedyncza zmienna.

-- Pod ifem może stać tylko int (może to się zmieni w późniejszych wersjach)
-- Dlatego też nie jest poprawne wyrażenie:
let k = if True then 1 else 0;;

-- Aplikować inta można tylko do funkcji typu a->a. Pomimo tego, że 
-- return (return (return 3)) ma pełen sens i to nawet bez przeładowań,
-- to jednak typ return jest a -> monada a, i nie unifikuje się z a->a.
-- Niepoprawny jest więc napis:
let k = 5 return 3;;

-- Przeładowana funkcja może się rekurencyjnie odwoływać tylko do swojego wariantu.
-- Dlatego to wyrażenie się nie otypuje:

let h (x:Int) = x;;
let h (x:Int->Int) = h (x 0);;