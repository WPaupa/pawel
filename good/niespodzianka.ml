-- Ten plik zawiera odwołania do większości pozostałych,
-- więc proszę o przeczytanie go na samym końcu.

-- *******************
-- *******************
-- *******************
-- *******************
-- *******************
-- *******************
-- *******************
-- *******************
-- *******************

-- No dobra, to mamy podstawowe operacje na listach,
-- mamy jakiś sposób reprezentacji ciągów znaków,
-- mamy monady i w szczególności monadę TCM,
-- oraz mamy sety i mapy. Mamy więc (z dokładnością
-- do obsługi wejścia i wyjścia) wszystko, z czego
-- korzystałem w Haskellu do napisania interpretera
-- tego języka. Możemy więc pokusić się o napisanie
-- self-interpretera Pawła w Pawle. Na potrzeby
-- tej demonstracji skorzystamy ze znacznie uproszczonej
-- wersji Pawła.

type Expr of = 
    EInt Int 
    | EVar (List of Int)
    | ELam (List of Int) (Expr of)
    | EApp (Expr of) (Expr of)
    | EIf (Expr of) (Expr of) (Expr of)
    | EArith (Expr of) (Expr of) (Int -> Int -> Int);;

-- Definiujemy mniej przeładowany operator binda
-- i mniej przeładowanego returna,
-- żeby szybciej się typowało
op left 1 >>= = bindReader;;
let bindReader (x:Reader of a b) f = {>>=} x f;;
let return a = Reader (λ_ . a);;

-- Kod zaadaptowany z pliku Calc.hs
let evalM expr = match expr with
    EInt a => return $ EInt a
    | EVar name => ask >>= (λenv. let q = lookup name env in match q with
        Just q' => evalM q'
        | Nothing => return $ EVar name
    )
    | EApp e1 e2 => (evalM e1) >>= (λe1'. match e1' with
            ELam name expr => (evalM e2) >>= (λe2'. local (insertMap name e2') $ evalM expr)
            | x => return $ EApp e1' e2
        ) 
    | EArith e1 e2 f => (evalM e1) >>= (λe1'. (evalM e2) >>= (λe2'. let pair = e1' ,, e2' in match pair with
            (EInt a) ,, (EInt b) => return $ EInt $ f a b
            | _ => return $ EArith e1' e2' f
        )) 
    | EIf e1 e2 e3 => (evalM e1) >>= (λe1'. match e1' with
            EInt a => if {==} a 0 then evalM e3 else evalM e2
            | _ => return $ EIf e1' e2 e3
        )
    | x => return x;;

let eval expr = runReader (evalM expr) emptyMap;;

let Y = 
ELam ([ 'f', ]) $ EApp 
    (ELam ([ 'x', ]) (EApp (EVar ([ 'f', ])) (
        EApp (EVar ([ 'x', ])) (EVar ([ 'x', ]))
    ))) 
    (ELam ([ 'x', ]) (EApp (EVar ([ 'f', ])) (
        EApp (EVar ([ 'x', ])) (EVar ([ 'x', ]))
)));;

let factorial = EApp Y (ELam ([ 'f', ]) (
    ELam ([ 'x', ]) (
        EIf (EVar ([ 'x', ])) (
            EArith (EVar ([ 'x', ])) (EApp (EVar ([ 'f', ])) (
                EArith (EVar ([ 'x', ])) (EInt 1) (λ x y . x - y)
            )) (λ x y. x * y)
        ) (
            EInt 1
        )
    )
));;

-- ^^ Notka ode mnie z przyszłości. W obecnym modelu to się pętli w nieskończoność,
-- zapewne przez jakiś brak leniwości. Nie miałem czasu
-- tego dokończyć. Self-interpreter będzie gotowy na drugi termin. 