# Język Paweł
Paweł jest czystym językiem funkcyjnym z (prawie)statyczną kontrolą typów. Jego składnia bazowana jest na składni języka OCaml.
## Podstawowa składnia
Program w języku Paweł jest serią deklaracji postaci:
- `let nazwa [argumenty] = wyrażenie`
- `type nazwa of [argumenty typowe] = [konstruktory typów oddzielone |]`
- `op left/right nazwa priorytet = konstruktor / nazwa procedury`

Ostatnia z tych konstrukcji jest definicją nowego infiksowego operatora dwuargumentowego.
Pierwsza z tych konstrukcji działa w trakcie wykonania i modyfikuje środowisko, natomiast druga i trzecia działają przed wykonaniem (w szczególności oznacza to, że język nie pozwala na typy zależne od wartości wyrażenia jak w λP, a operatory są tak naprawdę tylko aliasami dla funkcji lub konstruktorów). W przeciwieństwie do OCamla, konstrukcja `let` pozwala na rekurencję.
### Wyrażenia
Wyrażenia są następującej postaci:
```
Exp ::= Exp Exp | Exp Op Exp | let nazwa [argumenty] = Exp in Exp | λ [argumenty] . Exp | match nazwa with [Case] | if Exp then Exp else Exp
```
Gdzie Op jest jednym ze zdefiniowanych w preprocessingu operatorów lub operatorem +, -, *, /. 
Większość tych konstrukcji jest oczywista, pozostaje wyjaśnić składnię `Case`:
```
Case ::= Match => Exp
Match ::= _ | nazwa zmiennej | konstruktor ( [Match] )
```
Jako że operatory definiowane w kodzie są tylko aliasami na konstruktory, to można ich używać w matchach. 
### Typy wariantowe
Typy wariantowe (algebraiczne) są standardowe, jak w OCamlu. Mogą być rekurencyjne, przykład:
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
Kolejność generowanych przeładowań jest zgodna z kolejnością przeładowań używanych wewnętrznie funkcji, i idzie "od lewej", czyli najpierw generuje wszystkie przeładowania dla pierwszego wariantu najbardziej lewej funkcji, potem drugiego itd. Funkcje przeładowane mogą być rekurencyjne, ale przy wywołaniu rekurencyjnym widoczne jest tylko obecne przeładowanie oraz przeładowania zdefiniowane wcześniej. Przeładowana funkcja rekurencyjna dokładnie tak samo jest definiowana w kilku wersjach, przy czym jedna z wersji jest rekurencyjna. Na przykład:
```
let piecewiseAdd (x : Int) (y : Int) = x + y;;
let piecewiseAdd (x : List of Int) (y : List of Int) = let z = x, y in 
    match z with
        (h1, t1) , (h2, t2) => (piecewiseAdd (h1, h2)) , (piecewiseAdd (t1, t2))
        | _ => Empty;;
```
W programie stworzy dwa warianty funkcji `piecewiseAdd`, pierwszy trywialny, a drugi wołający i pierwszy i rekurencyjnie siebie samego.
## Aplikacja
W Pawle po lewej stronie aplikacji może stać dowolne wyrażenie. 
- Jeśli to wyrażenie wylicza się do funkcji, to jako semantyka aplikacji zostanie wykonana standardowa $\beta$-redukcja (tak jak w każdym innym języku)
- Jeśli to wyrażenie wylicza się do wartości `n` typu Int, to zostanie potraktowane jako funkcja typu $\forall\alpha.~(\alpha\to\alpha)\to(\alpha\to\alpha)$, która każdej funkcji `f` typu `a->a` przypisuje `n`-krotne złożenie funkcji `f` ze samą sobą (czyli `n` zostanie potraktowane jak liczebnik Churcha)
- Jeśli to wyrażenie wylicza się do typu wariantowego o konstruktorze `Cons a1 a2 ...`, to zostanie potraktowane jak funkcja, która każdemu argumentowi `f` przyporządkowuje wyrażenie o tym samym konstruktorze, postaci `Cons (a1 f) (a2 f) ...`. Innymi słowy, aplikacja typów wariantowych o argumentach będących funkcjami jest aplikacją tych funkcji.
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
Argumenty konstruktora aplikowanego typu wariantowego muszą być odpowiedniego typu. Na przykład w kodzie:
```
type Pair of a b = Cons a b;;
let g = Cons (λ x . 1) (λ x . x 1);;
let gf f = g f;;
```
`g` się otypuje poprawnie, ale `gf` już nie. Oznacza to, że pomimo tego, że wszystko jest w Pawle traktowane jako funkcja, to i tak nie ma poprawności $\eta$-redukcji.

Liczby naturalne są traktowane, jakby były typu $\forall \alpha.(\alpha\to\alpha)\to(\alpha\to\alpha)$, więc w szczególności mogą być zaaplikowane do siebie samych. Wartością termu `n m` jest liczba $m^n$, a to obliczenie jest wspierane z poziomu interpretera, więc potęga tym sposobem jest liczona szybko. Ponadto liczby można aplikować do typów wariantowych, a typy wariantowe do liczb, otrzymując przewidywalne wyniki:
```
2 ([a, b, c, ]) x = ([a, b, c, ]) (([a, b, c, ]) x)
([a, b, c, ]) 2 = [a 2, b 2, c 2, ]
```
Najciekawszą konsekwencją aplikacji dla list jest fakt, że z listy możemy łatwo stworzyć obiekt, który przyporządkowuje funkcji jej aplikację na wszystkich elementach tej listy. Innymi słowy:
```
map list = match list with Empty => Empty | h, t => (λ x . h x) , (map t);;
```
daje funkcję `map list function` znaną z innych języków.

Te reguły dla aplikacji nie sprawiają jednak, że typ `Int` jest traktowany dokładnie tak samo, jak typ `(a->a)->(a->a)`. To traktowanie jest jednostronne, czyli gdy funkcji, która wymaga argumentu typu `Int`, zostanie dany arugment typu `(a->a)->(a->a)`, dostaniemy błąd typów, ale gdy funkcji, która wymaga argumentu typu `(a->a)->(a->a)`, zostanie dany argument typu `Int`, błędu typów już nie będzie. Tak się dzieje dlatego, że pomimo tego, że wyrażalne w języku wyrażenia tych typów są takie same, to są one traktowane jak różne obiekty. Rozważane jest rozszerzenie do języka, w którym ta subtelność jest usunięta.
## Instrukcje warunkowe
Wyrażenie `if e1 then e2 else e3` jest de facto aliasem na funkcję `ifte e1 (λ _ . e2) (λ _ . e3)`. Funkcja `ifte` jest przeładowana dla argumentów `e1` typu `Int`, ale można ją dodatkowo przeładowywać dla wybranych przez siebie argumentów. Mamy, że `ifte x` jest funkcją `λ x y . x Force`, gdzie `Force` jest dowolnym wyrazem, gdy x jest niezerowe oraz funkcją `λ x y . y Force`, gdy x jest zerowe.

Do porównywania obiektów typu `Int` istnieją operatory `==`, `>`, `>=`, `<=` i `<`, wyliczające się do 1 lub 0 w standardowy sposób.
## Działania arytmetyczne
Działania arytmetyczne +, *, - i / są domyślnie przeładowane dla typu `Int` w standardowy sposób, ale można je przeładować dla dowolnych typów.
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

### Oczekiwane punkty
36