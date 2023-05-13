op right 4 == = {==};;
op right 4 /= = {/=};;
op right 4 <  = {<};;
op right 4 >  = {>};;
op right 4 <= = {<=};;
op right 4 >= = {>=};;
op left  6 +  = {+};;
op left  6 -  = {-};;
op left  7 /  = {/};;
op left  7 *  = {*};;
op left  7 mod = {mod};;
op right 8 ** = {**};;

let {mod} a b = a - (b * (a / b));;
let {**} a b = b ({*} a) 1;;