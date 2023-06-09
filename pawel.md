# Język Paweł
Paweł jest czystym językiem funkcyjnym ze statyczną kontrolą typów. Jego składnia bazowana jest na składni języka OCaml i częściowo Haskell.
## Podstawowa składnia
Program w języku Paweł jest serią deklaracji postaci:
- `let nazwa [argumenty] = wyrażenie`
- `type nazwa of [argumenty typowe] = [konstruktory typów oddzielone |]`
- `op left/right nazwa priorytet = konstruktor / nazwa procedury`

Ostatnia z tych konstrukcji jest definicją nowego infiksowego operatora dwuargumentowego.
Wszystkie te konstrukcje działają w czasie wykonania, z normalnymi zasadami przesłaniania (z wyjątkiem przeładowań, dodanie nowego przeładowania nie przysłania starych, więcej o tym później). W przeciwieństwie do OCamla, konstrukcja `let` pozwala na rekurencję.
### Wyrażenia
Wyrażenia są następującej postaci:
```
Exp ::= Exp Exp | Exp Op Exp | let nazwa [argumenty] = Exp in Exp | λ [argumenty] . Exp | match nazwa with [Case] | if Exp then Exp else Exp
```
Gdzie Op jest jednym ze zdefiniowanych w języku operatorów. 
Większość tych konstrukcji jest oczywista, pozostaje wyjaśnić składnię `Case`:
```
Case ::= Match => Exp
Match ::= _ | nazwa zmiennej | konstruktor ( [Match] )
```
Jako że operatory definiowane w kodzie są tylko aliasami na konstruktory, to można ich używać w matchach. 
### Typy wariantowe
Typy wariantowe (algebraiczne) są standardowe, jak w Haskellu. Mogą być rekurencyjne, przykład:
```
type List of a = Empty | Cons a (List of a);;
```
## Polimorfizm
Paweł wspiera dwa rodzaje polimorfizmu: polimorfizm wynikający z systemu typów oraz polimorfizm ad hoc.
### Polimorficzne typy
System typów Pawła opiera się na systemie Hindley-Milner (z modyfikacjami opisanymi w sekcjach Przeładowywanie i Aplikacja). Oznacza to,
że każda funkcja domyślnie ma najogólniejszy typ, który da się jej przypisać. Na przykład funkcja `f` zadeklarowana przez:
```
let f x y = x;;
```
ma typ $\forall\alpha\beta.~\alpha\to\beta\to\alpha$. Paweł tę funkcję otypuje jako `a -> b -> a` i pozwoli jako jej argumenty
przekazywać dowolne dwie zmienne. 
### Przeładowywanie
Przy każdym argumencie funkcji można sprecyzować jej typ. Jeśli tego się dokona, do środowiska zostanie dopisana wersja tej funkcji, która działa tylko dla tego typu. Jeśli w późniejszym miejscu w kodzie zostanie zadeklarowana funkcja o tej samej nazwie, ale z innymi sprecyzowanymi typami argumentów, to nie przysłoni ona tej funkcji, ale zostanie dodana do listy możliwych przeładowań. W podstawowej wersji Pawła typy argumentów przeładowań nie mogą być polimorficzne, ale rozważane jest rozszerzenie z tą funkcjonalnością. Na przykład kod:
```
let f (x : Int) y = x + 1;;
let f (x : (Int -> Int)) y = y;;
let g y = f (λ x . y);;
```
zostanie poprawnie sparsowany i wykonany. Jeśli dwa przeładowania funkcji pasują do konkretnego przypadku, to wybierane jest to zadeklarowane wyżej.

To zachowanie jest podobne do klas w Haskellu, ale jest trochę inaczej traktowane przez system typów. Przy tworzeniu funkcji korzystającej z funkcji przeładowanych tworzą się jej wersje dla każdego dobrze typującego się zestawu przeładowań. Na przykład w powyższym przykładzie stworzy się tylko jedna wersja, typu `Int -> a -> a`. Natomiast dla funkcji:
```
type Bool = True | False;;
let h (x : Int) (y : Bool) = x;;
let h (x : Bool) (y : Int) = y;;
let h (x : Int) (y : Int) = x;;
let h (x : Bool) (y : Bool) = 0;;
let i x y z = h (h x y) z;;
```
Stworzy się osiem przeładowań dla funkcji `i` (i osiem zostanie odrzuconych ze względu na niezgodność typów), czyli efekt ostatniej linijki będzie taki sam, jak gdyby napisać kod:
```
let i (x : Int) (y : Bool) (z : Bool) = h (h x y) z;;
let i (x : Int) (y : Bool) (z : Int) = h (h x y) z;;
itd.
```
Kolejność generowanych przeładowań jest zgodna z kolejnością przeładowań używanych wewnętrznie funkcji, i idzie "od lewej", czyli najpierw generuje wszystkie przeładowania dla pierwszego wariantu najbardziej lewej funkcji, potem drugiego itd. Funkcje przeładowane mogą być rekurencyjne, ale przy wywołaniu rekurencyjnym widoczne jest tylko obecne przeładowanie. Przeładowana funkcja rekurencyjna dokładnie tak samo jest definiowana w kilku wersjach. Na przykład poniższy kod jest błędny:
```
op right 5 ,, = ConsP;;
let piecewiseAdd (x : Int) (y : Int) = x + y;;
let piecewiseAdd (x : List of Int) (y : List of Int) = let z = x ,, y in 
    match z with
        (h1, t1) ,, (h2, t2) => (piecewiseAdd h1 h2) , (piecewiseAdd t1 t2)
        | _ => Empty;;
```
Natomiast gdyby zastąpić `piecewiseAdd h1 h2` przez `h1 + h2`, otrzymamy poprawny kod.
## Aplikacja
W Pawle po lewej stronie aplikacji może stać dowolne wyrażenie. 
- Jeśli to wyrażenie wylicza się do funkcji, to jako semantyka aplikacji zostanie wykonana standardowa $\beta$-redukcja (tak jak w każdym innym języku)
- Jeśli to wyrażenie wylicza się do wartości `n` typu Int, to zostanie potraktowane jako funkcja typu $\forall\alpha.~(\alpha\to\alpha)\to(\alpha\to\alpha)$, która każdej funkcji `f` typu `a->a` przypisuje `n`-krotne złożenie funkcji `f` ze samą sobą (czyli `n` zostanie potraktowane jak liczebnik Churcha)
- Jeśli to wyrażenie wylicza się do typu wariantowego o konstruktorze `Cons a1 a2 ...`, to zostanie potraktowane jak funkcja, która każdemu argumentowi `f` przyporządkowuje wyrażenie o tym samym konstruktorze, postaci `Cons (a1 f) (a2 f) ...`. Innymi słowy, aplikacja typów wariantowych o argumentach będących funkcjami jest aplikacją tych funkcji. To zachowanie jest obecnie wspierane
przez funkcję wykonującą, ale nie przez system typów. Dzieje się tak, żeby nie powstawało
za dużo przeładowań prostych funkcji. W przyszłych wersjach Pawła tę funkcję będzie można
włączyć lub wyłączyć za pomocą argumentu wykonania.
Przykłady:
```
let dziesiec = (λ x . x * 2) 5;;
let trzydziesci_dwa = 5 (λ x . x * 2) 1;;

type List of a = Empty | Cons a (List of a);;
op right 5 , = Cons;;
let [ x = x;;
let ] = Empty;;
let parzyste = ([ (λ x . x * 1), (λ x . x * 2), (λ x . x * 3), ]) 2;;
```
Wartość `dziesiec` wyliczy się do dziesięciu, wartość `trzydziesci_dwa` do 32. Najciekawszym przykładem jest wartość wartość `parzyste`, jej wyliczenie schematycznie będzie wyglądało tak:
```
([ λ x . x * 1, λ x . x * 2, λ x . x * 3, ]) 2 = 
    (λ x . x * 1, (λ x . x * 2, λ x . x * 3)) 2 = ((λ x . x * 1) 2 , ((λ x . x * 2, λ x . x * 3) 2)) =
    2, ((λ x . x * 2) 2, (λ x . x * 3) 2) =
    2, (4, 6) =
    [ 2 , 4 , 6 , ]
```
W tym kodzie widać również przykład tego, jak można użyć konstrukcji `op` do zdefiniowania lukru syntaktycznego na listach zupełnie z poziomu języka.
### Konsekwencje aplikacji
Liczby naturalne są traktowane, jakby były typu $\alpha.(\alpha\to\alpha)\to(\alpha\to\alpha)$ (monomorficznego!), w szczególności nie mogą być zaaplikowane do siebie samych. Ponadto system typów dla dobra programisty zabrania aplikowania liczb do funkcji z i do liczb, żeby nie tworzyło się za dużo przeładowań (w szczególności żeby typy `a->Int` oraz `Int` były odróżnialne).

Typ `Int` jest traktowany w większości pozostałych przypadków dokładnie tak samo, jak typ `(a->a)->(a->a)`. Gdy funkcji, która wymaga argumentu typu `Int`, zostanie dany arugment typu `(a->a)->(a->a)`, dostaniemy poprawnie typujące się wyrażenie, w którym funkcji zostanie przypisana wartość inta (odpowiednie twierdzenia z rachunku lambda gwarantują nam, że każda funkcja tego typu jest odpowiednikiem inta).
## Instrukcje warunkowe
Wyrażenie `if e1 then e2 else e3` wykonuje najpierw `e1`, a potem w zależności od tego, czy wyliczy się do niezerowej wartości czy zera, `e2` lub `e3` (w szczególności jeśli `e1` nie jest prawdą, to wykonanie nigdy nie wejdzie do `e2`, podobnie jak przy lambdach). Pod ifem musi być Int, nie tylko moralnie, ale także literalnie.

Do porównywania obiektów typu `Int` istnieją operatory `==`, `>`, `>=`, `<=` i `<`, wyliczające się do 1 lub 0 w standardowy sposób.
## Działania arytmetyczne
Działania arytmetyczne +, *, - i / są domyślnie przeładowane dla typu `Int` w standardowy sposób, ale można je przeładować dla dowolnych typów. Składniowo te działania są zdefiniowanymi w języku operatorowymi aliasami dla funkcji `{+}`, `*`, `{-}` i `{/}` z priorytetami jak w Haskellu. 
### Kolejność wykonywania działań
Bazowo ciąg aplikacji jest parsowany jako lista, w której potem operatory są zamieniane syntaktycznie na funkcje zgodnie z precedencją. Na przykład funkcja `h` w kodzie:
```
op right 5 , = Cons;;
op left 7 mod = {mod};;
let k = 5;;
let h = k k , k , k mod k mod k , ];;
```
zostanie sparsowana do listy `{"k"; "k"; ","; "k"; ","; "k"; "mod"; "k"; "mod"; "k"; ","; "]"}`, która potem zostanie zinterpretowana tak samo, jak gdyby funkcja `h` była zapisana z nawiasami:
```
let h = (((k k) , k) , ((k mod k) mod k)) , ];;
```
Poziomy precedencji mogą być liczbami jednocyfrowymi, dla operatorów arytmetycznych z języka są takie same, jak w Haskellu (6 dla dodawania i odejmowania, 7 dla mnożenia i dzielenia). Precedencja funkcji jest naturalna, na przykład w:
```
let h = k k + k k k;;
```
liczba `h` sparsuje się jako `(k k) + ((k k) k)`.

Precedencja operatorów nie ma znaczenia w pattern-matchingu. W konstrukcji match operatory są parsowane "od lewej", a konstruktory prefiksowe wiążą do końca matcha lub nawiasu. Na przykład:
```
let f x = match x with
    Constructor a , b c => a
    | Constructor2 (a , b , c) => a;;
```
zmatchuje `x` z konstruktorem `Constructor` na zmiennych `a`, `,`, `b` i `c` (co będzie prowadzić do błędów, skoro `,` jest zdefiniowany także jako operator) oraz z `Constructor2 (Cons a (Cons b c))`, gdzie `Cons` to syntaktyczny odpowiednik operatora `,` (czyli match jest intuicyjnie poprawny zgodnie z definicją użytą wyżej). 

# Wyjaśnienia
## Gramatyka
Formalna gramatyka języka w formacie LBNF:
```
entrypoints Program;

Prog . Program ::= [Decl];

DExp . Decl ::= "let" Idt [ TypeDecl ] "=" Exp;
DLOp . Decl ::= "op left" Integer Idt "=" Idt;
DROp . Decl ::= "op right" Integer Idt "=" Idt;
DType . Decl ::= "type" Idt "of" [ Idt ] "=" [ Variant ];
VarType . Variant ::= Idt [ Type1 ];

TInt . Type1 ::= "Int";
TVar . Type1 ::= Idt;
TFunc . Type ::= Type1 "->" Type;
TVariant . Type ::= Idt "of" [ Type1 ];
coercions Type 1;

EUnparsed . Exp ::= [ Exp1 ];
EVar . Exp1 ::= Idt;
EInt . Exp1 ::= Integer;
ELet . Exp1 ::= "let" Idt [ TypeDecl ] "=" Exp "in" Exp;
EIf  . Exp1 ::= "if" Exp "then" Exp "else" Exp;
ELam . Exp1 ::= "λ" [ Idt ] "." Exp;
EMatch . Exp1 ::= "match" Idt "with" [ MatchCase ];

_    . Exp1 ::= "(" Exp ")";

Case . MatchCase ::= Match "=>" Exp;

MVar  . Match1 ::= Idt;
MList . Match  ::= [ Match1 ];
_     . Match1 ::= "(" Match ")";

TDVar  . TypeDecl ::= Idt;
TDType . TypeDecl ::= "(" Idt ":" Type ")";

token Idt (((letter | '_' | '\'' | '{' | '}') (letter | '_' | '\'' | '{' | '}' | digit) *) | ('[' | ']' | '_' | '\'' | '*' | '+' | '/' | '-' | '{' | '}' | '|' | '$' | '>' | '=' | '<' | ',' | '?' | ':' | '.' | '!' | '&')+);

comment "--" ;
comment "(*" "*)" ;

terminator Decl ";;";
separator Variant "|";
separator MatchCase "|";
separator Type1 "";
separator Idt "";
separator Exp1 "";
separator Match1 "";
separator TypeDecl "";
```
W tej gramatyce pojawiają się konflikty shift/reduce. Wszystkie te konflikty są przy regułach przypadków brzegowych dla list:
```
[ MatchCase ] -> 
[ MatchCase ] -> MatchCase
[ Exp1 ] -> 
```
Priorytetyzacja shift nad reduce w poprawny sposób sprawia, że listy nie są kończone przedwcześnie, więc wszystkie konflikty są rozwiązywane w poprawny sposób. 
## Przykłady
### Potęgowanie
```
let id x = x;;
let multiply n m = n * m;;
let {*} (x : a -> Int) (y : Int) = λ a . (x a) * y;;
let {+} (x : a -> Int) (y : Int) = λ a . (x a) + y;;

let power1 n m = if m then n * (power n (m - 1)) else 1;;
let power2 n m = m (multiply n) 1;;
let power3 n m = m (id * n) 1;;
let power4 n m = m n;;
```
To, czy typ wynikowy ostatniego przykładu będzie zgodny z typem `Int`, zależy od wersji języka.
### Rekurencyjne przeładowywanie
Jako że wiązanie przeładowań funkcji jest statyczne, to rekurencyjna funkcja przeładowana musi zawsze wołać ten sam wariant siebie w tym samym miejscu. Na przykład **niepoprawnym** kodem jest:
```
let {*} (x : a -> b) (y : a -> b) = λ a . (x a) * (y a);;
let e = (λ x y . 5) * (λ x y . 3);;
```
Bo w wyrażeniu `e` zostanie dopasowane napisane wyżej przeładowanie funkcji `*`, w którym natomiast znowu zostanie dopasowane ono samo (rekurencyjnie). Taka rekurencja nie ma warunku początkowego, bo funkcja `{*}` napisana w kodzie jest związana ze samą sobą, więc nie może być związana z mnożeniem obiektów typu `Int`. Z tego powodu w języku są definiowane nowe funkcje `[+]`, bazowo przeładowane, do których potem jest przypisany operator.
### Silnia
Silnię oczywiście można napisać tak jak w OCamlu, ale niżej przedstawiono bardziej Pawłowy sposób pisania silni.
```
let fst x = match x with (a ,, b) => a;;
let snd x = match x with (a ,, b) => b;;
let foldp f x = match x with (a ,, b) => f a b;;

let {$} f x = f x;;
op right 0 $ = {$};;

let pairFunctions f g = λ x . (f x) ,, (g x);;

let factorial n = snd $ n (pairFunctions (fst + 1) (foldp {*})) (0 ,, 1);;
```
## Kod
Kod prezentowany w tym dokumencie nie korzysta z założeń istnienia wcześniejszych bibliotek, ale niektóre fragmenty korzystają z funkcji, przeładowań i operatorów zdefiniowanych w poprzednich fragmentach. W języku Paweł planowana jest biblioteka standardowa, do której będą należeć niektóre ze zdefiniowanych w tym dokumencie funkcji.
### Tabelka 
Cechy od 1 do 16 zostały zrealizowane, natomiast cecha 17 (sprawdzanie kompletności matcha) - jeszcze nie.
### Oczekiwane punkty
36
## Użycie
Pawła można używać z konsoli poprzez `./interpreter` lub z pliku (lub plików) poprzez `./interpreter pliki`. Przykłady w folderze `good` często korzystają z rzeczy zadeklarowanych w innych plikach, w takim wypadku na górze pliku zapisano poprawne użycie. Oprócz tego jako jeden (lub kilka) z plików można podać `stdin`, wtedy wejście w danym momencie zamiast pliku jest brane z konsoli.
