#use "DefInterpreter.ml";;

let gamma v = match v with
        S str -> (match str with 
                        "x" -> AnswerInt(10)
                        |"y" -> AnswerInt(5)
                        | "true" -> AnswerBool(true)
                        | "false" -> AnswerBool(false)
                        | "random" -> AnswerInt(11)
                        |_ -> AnswerInt(2) )
        | _ -> AnswerInt(1)                
        

let e1 = (Gt( Mod(Const(-3) ) , Const(2) ))
let g1 = AnswerBool(true)

let e2 = (Lt( Mod(Const(-3) ) , Const(3) ))
let g2 = AnswerBool(false)

let e3 = Tuple ([e1;e2])
let g3 = AnswerTuple ([g1;g2])

let e4 = Proj(1, e3 )
let g4 = g2 

let e5 = Var ( S "x" )
let g5 = AnswerInt(10)
let e6 = Var ( S "y" )
let g6 = AnswerInt(5)

let e7 = Pow (e5,e6)
let g7 = AnswerInt(100000)

let e8 = EqI(Sub(Add(Const(2),Const(3)), Const(5)),Const(0))
let g8 = AnswerBool(true)

let e9 = Div( Mul(Pow(Const(2), Const(10)), Const(4)), Const(1024) )
let g9 = AnswerInt(4)

let e10 = Impl(Gt(Add(Var (S "x"), Const(80)), Const(80)), Var( S "true"))
let g10 = AnswerBool(true)

let e11 = Not(Or(e8, Var (S "random")))
let g11 = AnswerBool(false)

let e12 = Gt(Mod(Const(-34)), Const(0))
let g12 = AnswerBool(true)

let e13 = Tuple ([e8; e9; e10; e11; e12]) (* == [true, 4, true, false, true] *)
let g13 = AnswerTuple([g8;g9;g10;g11;g12])

let e14 = Proj (3, e13) (* == exp3 false *)
let g14 = g11

let e15 = Not ( And (e14, false))
let g15 = AnswerBool(true)


let l = [e1;e2;e3;e4;e5;e6;e7;e8
        ;e9;e10;e11;e12;e13;e14;e15
        ];;

let gt = [g1;g2;g3;g4;g5;g6;g7;g8
        ;g9;g10;g11;g12;g13;g14;g15
        ];;

let rec checker i (l , gtr) = match (l,gtr) with
        ([],[]) -> ()
        | (x::xs,y::ys) -> ((if((execute ([],gamma,(compile x))) <> y ) then (Printf.printf "Execute(compile) =/= ground Truth for: %d\n " i) 
                        else if ((eval gamma x) <> y ) then (Printf.printf "Eval =/= ground Truth for %d\n: " i)
                        else (Printf.printf "Success for: %d\n" i ) ) ; checker (i+1) (xs,ys) );;


checker 0 (l,gt);;