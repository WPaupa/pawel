type Stack of a = Stack (List of a);;
let push a (s:Stack of a) = match s with Stack l => Stack (a, l);;
let pop (s:Stack of a) = match s with Stack (h, t) => h ,, Stack t;;
let get (s:Stack of a) = match s with Stack (h, t) => h;;
let isEmpty (s:Stack of a) = match s with 
    Stack [] => 1
    | a => 0;;
let emptyStack = Stack [];;

type Queue of a = Queue (List of a) (List of a);;
let push a (q:Queue of a) = match q with Queue inp out => Queue (a, inp) out;;
let pop (q:Queue of a) = match q with 
    Queue inp (h, t) => h ,, (Queue inp t)
    | Queue inp Empty => pop (Queue Empty (reverse inp));;
let isEmpty (q:Queue of a) = match q with
    Queue Empty Empty => 1
    | a => 0;;
let emptyQueue = Queue [] [];;

-- Kod kolejki priorytetowej przepisany 
-- z mojego rozwiązania zadania Drzewa lewicowe na WPF
type pQueue of a = PNull | PNode (pQueue of a) (pQueue of a) a Int;;
let sval a = match a with
    PNull => 0
    | PNode _ _ _ v => v;;

let isEmpty (q:pQueue of a) = match q with
    PNull => 1
    | a => 0;;

-- Tutaj używamy {+} zamiast przeciążonych operatorów infiksowych,
-- żeby pomóc binderowi - i tak dostajemy tylko przeładowanie dla inta,
-- a gdy operatory są przeładowane, to najpierw musi się stworzyć
-- każda możliwa opcja, a potem dopiero otypować. W tym wypadku
-- trwa to naprawdę długo.
let join (a:pQueue of a) (b:pQueue of a) = let k = a ,, b in match k with
    PNull ,, b => b
    | a ,, PNull => a
    | (PNode al ar akey asval) ,, (PNode bl br bkey bsval) =>
        if akey <= bkey then
            let r = join ar b in 
                if isEmpty al 
                    then PNode r al akey 1
                    else if sval r <= sval al
                        then PNode al r akey ({+} 1 $ sval r)
                        else PNode r al akey ({+} 1 $ sval al)
        else let r = join br a in
            if isEmpty bl
                then PNode r bl bkey 1
                else if sval r <= sval bl
                    then PNode bl r bkey ({+} 1 $ sval r)
                    else PNode r bl bkey ({+} 1 $ sval bl);;
let pop (q:pQueue of a) = match q with
    PNode l r key _ => key ,, join l r;;
let push a (q:pQueue of a) = join q (PNode PNull PNull a 1);;
let get (q:pQueue of a) = match q with
    PNode _ _ key _ => key;;
let emptypQueue = PNull;;