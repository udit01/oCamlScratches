(* #use "DefInterpreter.ml" *)
(* Note:
 * Please make suitable changes to the shared test cases so that
 * the constructors match your signature definition.
 *)

(*--==Compile & Execute==--*)

let e1 = Add(Const(1),Const(2));;
execute ([],gamma,(compile e1)) ;;
let e2 = Mul(Const(6),Const(6));;
execute ([],gamma,(compile e2)) ;;
let e3 = Pow(Const(2),Const(4));;
execute ([],gamma,(compile e3)) ;;
let e4 = Div(Const(6),Const(3));;
execute ([],gamma,(compile e4)) ;;
let e5 = Var(S "iden1");;
execute ([],gamma,(compile e5)) ;;
let e6 = Var(S "iden2");;
execute ([],gamma,(compile e6)) ;;

let e7 = Mod(Const(-1));;
execute ([],gamma,(compile e7)) ;;
let e8 = Proj(2,Tuple([Const(12);Const(121);Const(33)]));;
execute ([],gamma,(compile e8)) ;;


let e9 = Sub(Proj(2,Tuple[Const(2);Const(5);Const(8)]),Const(1));;
execute ([],gamma,(compile e9)) ;;
let e10 = Mod(Proj(2,Tuple[Const(2);Const(5);Const(8)]));;
execute ([],gamma,(compile e10)) ;;


let e11 = Or(
	EqI(Const(5),Const(5)),
	And(EqI(Sub(Const(2),Const(1)),Const(1)),
		Mod(Proj(2,Tuple[Const(2);Const(5);Const(8)]))
	)
);;
execute ([],gamma,(compile e11)) ;;

let e12 = And((true), (false));;
execute ([],gamma,(compile e12)) ;;

let e13 = Impl(Not(Impl(Or((true), (false)), And((true), (false)))),Impl(And((true), (false)), Or((true), (false))));;
execute ([],gamma,(compile e13)) ;;

let e14 = Gte(Const(4),Const(2));;
execute ([],gamma,(compile e14)) ;;

let e15 = Lte(Const(4),Const(2)) ;;
execute ([],gamma,(compile e15)) ;;

(* We weren't even told what was if then else till then *)
(* Ifthenelse *)
(* let e16 = ( Gt(Const(4),Const(2)) , Add(Const(1),Const(3)), Sub(Const(1),Const(3)) ); *)

(* 
Other things that I have implemented are Xor , Max, Min, Var 15 examples given in the code itself
*)

(* let e11 =Or(
	EqI(Const(5),Const(5)),
	And(EqI(Sub(Const(2),Const(1)),Const(1)),
		Gt( Mod(Proj(2,Tuple[Const(2);Const(5);Const(8)])),Const(2))
	)
);; *)