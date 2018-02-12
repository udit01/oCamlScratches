#use "DefInterpreter.ml";;

let g v = match v with
        S str -> (match str with 
                        "x" -> AnswerInt(10)
                        |"y" -> AnswerInt(20))
                        |_ -> AnswerInt(30)
        | _ -> AnswerInt(1)                
        ;;

let e1 = (Gt( Mod(Const(-3) ) , Const(2) ));;
let e2 = (Gt( Mod(Const(-3) ) , Const(3) ));;
let e3 = Tuple ([e1;e2])
let e4 = Proj(1, e3 );;

let l = [e1;e2;e3;e4];;

let rec checker i l = match l with
        [] -> ()
        | x::xs -> ((if(execute ([],g,(compile x)) = eval g x ) then (Printf.printf "Good for for %d\n" i) else 
                        (Printf.printf "Error for %d\n" i)) ; checker (i+1) xs );;