#use "DefInterpreter.ml";;

let g1 v = match v with
        B b -> (match b with 
                    b1 -> AnswerBool(true)
                    | b2 -> AnswerBool(false)
                    | _ -> AnswerBool(true))
        | I i -> (match i with 
                        i0 -> AnswerInt(0)
                        |i1 -> AnswerInt(1)
                        |i2 -> AnswerInt(2)
                        | _ -> AnswerInt(3))
        | S str -> (match str with 
                        "x" -> AnswerInt(10)
                        |"y" -> AnswerInt(20))
                        |_ -> AnswerInt(30)
        ;;

let e1 = (Gt( Mod(Const(-3) ) , Const(2) ));;
let e2 = (Gt( Mod(Const(-3) ) , Const(3) ));;

let ocl = compile e1;;
let ocl2 = compile e2;;

execute ([],g1,ocl);;
execute ([],g1,ocl2);;


let t1 = Mod(Const(-1));;
eval g1 t1;;
let l1 = compile t1;;
execute ([],g1,l1);;


let e1 = (Gt( Mod(Const(-3) ) , Const(2) ));;
let a1 = eval g1 e1 ;;
let o1 = compile e1;;
let a2 = execute ([], g1, o1);;
a1=a2;;

compile (Const(2));;
compile (Const(-2));;
compile ( Mod(Const(-2)));;

(* Check for varialbes *)
