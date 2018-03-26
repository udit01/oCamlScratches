(* O and C are written in capital and are constructors *)
type t = O | C of t ; 

(* this count is recursive and takes O(n) time and space *)
let rec count_t t = match t with 
O -> 0
| C(p) -> 1 + (count_t t);;

(* this count is tail-recursive and takes O(n) time but O(1)space *)
let rec count_t t e = match t with
O -> e (*return the value of e accumulated till now*)
| C(p) -> (count_t p (1+e));;

(* sum of type t  OF ORDER O(count t1)*)
let rec sum_t t1 t2 = match t1 with
O -> t2 
| C(p) -> C (sum_t p t2) ;;

(* how can we optimize sum ? other than checking the minimum? something like tail recursion? *)

(*writing a product function ? Then make a PL and interpreter*)
