(* File for testing 
 *)

(* Pattern matching testing *)
(* 
execption NotFound;;
let lookup list v = match list with
        l1 @ [(v,i)] @ l2 -> i
        | _ -> raise NotFound
        ;;

let ll = [("a",1);("b",2);("c",3;("d",4);("z",26)]
;;

lookup ll "c";; *)
(* 
^ The above doesn't work because @ is operator not a symbol, 
A list IS .. 1::2::3::4::[] etc, but @ just returns something

Where to get these concepts cleared ? *)