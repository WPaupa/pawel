op right 0 $  = [$];;
op right 2 || = [||];;
op right 3 && = [&&];;
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
op left  7 mod = [mod];;
op right 8 ^  = [^];;

op right 0 ,  = Cons;;
op right 5 :: = Cons;;
op right 5 ++ = [++];;
op right 5 in = [in];;

let id x = x;;