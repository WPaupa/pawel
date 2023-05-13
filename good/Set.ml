-- użycie: ./Conn good/regularAri.ml good/Prelude.ml good/String.ml good/Set.ml
-- (można także bez String.ml, ale wtedy nie można tworzyć map o kluczu łańcuchowym)

-- Implementacja zbiorów (drzewo AVL) z zadania iSet z WPF.
-- Dla szybkości parsowania tutaj należy korzystać z regularAri

type AVL of a = SEmpty | SNode (AVL of a) a (AVL of a) Int;;

type Set of a = Set (a -> a -> Int) (AVL of a);;

let cmp (x:Set of a) = match x with
    Set cmp set => cmp;;
let set (x:Set of a) = match x with
    Set cmp set => set;;

let height (x:AVL of a) = match x with
    SNode _ _ _ h => h
    | SEmpty => 0;;

let make (l:AVL of a) k (r:AVL of a) = SNode l k r (max (height l) (height r) + 1);;

let bal l k r = 
    let hl = height l in
    let hr = height r in 
    if hl > hr + 2 then 
        match l with
            SNode ll lk lr _ => 
                if height ll >= height lr then make ll lk (make lr k r)
                -- tutaj w ocamlu ten match musiał być w nawiasie, żeby odróżnić
                -- jego case od case'a zewnętrznego matcha, ale w Pawle akurat
                -- parsuje się poprawnie
                else match lr with
                    SNode lrl lrk lrr _ => make (make ll lk lrl) lrk (make lrr k r)

    else if hr > hl + 2 then
        match r with
            SNode rl rk rr _ =>
                if height rr >= height rl then make (make l k rl) rk rr
                else match rl with
                    SNode rll rlk rlr _ => make (make l k rll) rlk (make rlr rk rr)
    else SNode l k r (max hl hr + 1);;

let min_elt (s:AVL of a) = match s with
    SNode SEmpty k _ _ => k
    | SNode l _ _ _ => min_elt l;;

let remove_min_elt (s:AVL of a) = match s with
    SNode SEmpty _ r _ => r
    | SNode l k r _ => bal (remove_min_elt l) k r;;

let merge (t1:AVL of a) (t2:AVL of a) = let k = t1 ,, t2 in 
    match k with
        SEmpty,, _ => t2
        | _ ,, SEmpty => t1
        | _ => bal t1 (min_elt t2) (remove_min_elt t2);;

let emptySet cmp = Set cmp SEmpty;;
let compare a b = if a < b then 0-1 else a > b;;
let emptySetC = emptySet compare;;

let isEmpty (s:Set of a) = let k = set s in match k with
    SEmpty => 1
    | _ => 0;;

-- Procedura wstawiania do AVLa musi się nazywać
-- inaczej niż procedura wstawiania do seta, 
-- żeby procedura wstawiania do seta mogła ją
-- wywołać (procedury mogą rekurencyjnie wołać tylko siebie)
let add_one cmp x (s:AVL of a) = match s with
    SNode l k r h => let c = cmp x k in
        if c == 0 then SNode l x r h
        else if c < 0 
            then let nl = add_one cmp x l in bal nl k r
            else let nr = add_one cmp x r in bal l k nr
    | SEmpty => SNode SEmpty x SEmpty 1;;

let insert x (s:Set of a) = match s with
    Set cmp set => Set cmp (add_one cmp x set);;

let join cmp (l:AVL of a) v (r:AVL of a) = let k = l ,, r in match k with
    SEmpty ,, _ => add_one cmp v r
    | _ ,, SEmpty => add_one cmp v l
    | (SNode ll lv lr lh) ,, (SNode rl rv rr rh) =>
        if lh > rh + 2 then bal ll lv (join cmp lr v r) else 
        if rh > lh + 2 then bal (join cmp l v rl) rv rr else 
        make l v r;;

-- W wersji z OCamla procedura split zwracała trójkę
-- (elementy po lewej, czy w drzewie znaleziono element, elementy po prawej)
-- Ale w Pawle nie ma natywnie krotek, więc para jest naturalniejsza i prostsza w obsłudze
let split x (st:Set of a) = 
    let loop cmp x s = match s with
        SEmpty => SEmpty ,, SEmpty
        | SNode l v r _ => let c = cmp x v in
            if c == 0 then l ,, r
            else if c < 0 then (
                let k = loop cmp x l in match k with
                    ll ,, rl => ll ,, join cmp rl v r
            ) else (
                let k = loop cmp x r in match k with
                    lr ,, rr => join cmp l v lr ,, rr
            ) in
    let k = loop (cmp st) x (set st) in match k with
        setl ,, setr => (Set (cmp st) setl) ,, (Set (cmp st) setr);;

let remove x (st:Set of a) =
    let loop cmp s = match s with
        SNode l k r _ => 
            let c = cmp x k in
                if c == 0 then merge l r else 
                if c < 0 then bal (loop cmp l) k r
                else bal l k (loop cmp r)
        | SEmpty => SEmpty in 
    match st with
        Set cmp set => Set cmp (loop cmp set);;

let exists x (st:Set of a) =
    let loop cmp s = match s with
        SNode l k r _ => let c = cmp x k in 
            (c == 0) || loop cmp (if c < 0 then l else r) 
        | SEmpty => 0 in 
    match st with 
        Set cmp set => loop cmp set;;

let map f (st:Set of a) =
    let loop cmp s = match s with
        SEmpty => SEmpty
        | SNode l k r h => SNode (loop cmp l) (f k) (loop cmp r) h in
    match st with
        Set cmp set => loop cmp set;;

let fold f (st:Set of a) acc =
    let loop cmp acc s = match s with
        SEmpty => acc
        | SNode l k r _ => loop cmp (f k (loop cmp acc l)) r in 
    match st with
        Set cmp set => loop cmp acc set;;

-- Mapy mamy gratis
let emptyMap = emptySet (λx y. let k = x ,, y in match k with
    (k1,,v1) ,, (k2,,v2) => compare k1 k2
);;
let insertMap k v map = insert (k ,, v) map;;

-- Analogicznie do exists
let lookup x (st:Set of (Pair of a b)) =
    let loop s = match s with
        SNode l (key ,, val) r _ => let c = compare x key in 
            if c == 0 then Just val
            else loop (if c < 0 then l else r) 
        | SEmpty => Nothing in 
    match st with 
        Set cmp set => loop set;;