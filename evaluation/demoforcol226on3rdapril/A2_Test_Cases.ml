(* Note:
 * Please make suitable changes to the shared test cases so that
 * the constructors match your signature definition.
 *)

(*--==Compile & Execute==--*)

Add(Const(1),Const(2));;
Mul(Const(6),Const(6));;
Pow(Const(2),Const(4));;
Div(Const(6),Const(3));;
Var(S "iden1");;
Var(S "iden2");;

Mod(Const(-1));;
Proj(2,Tuple([Const(12);Const(121);Const(33)]));;

Sub(Proj(2,Tuple[Const(2);Const(5);Const(8)]),Const(1));;
Mod(Proj(2,Tuple[Const(2);Const(5);Const(8)]));;

Or(
	EqI(Const(5),Const(5)),
	And(EqI(Sub(Const(2),Const(1)),Const(1)),
		Gt( Mod(Proj(2,Tuple[Const(2);Const(5);Const(8)])),Const(2))
	)
);;

And((true), (false));;
Impl(Not(Impl(Or((true), (false)), And((true), (false)))),Impl(And((true), (false)), Or((true), (false))));;

Gte(Const(4),Const(2));;
Lte(Const(4),Const(2));;

(* We weren't even told what was if then else till then *)
(* Ifthenelse *)
( Gt(Const(4),Const(2)) , Add(Const(1),Const(3)), Sub(Const(1),Const(3)) );

(* Lambda is a lambda function of type exp*exp and LetinEnd is a ternary operator of type exp*exp*exp *)
(* Apply( Lambda(Var("x"), LetinEnd(Para[Assgn(Var("a"),Const(2))],Add(Var("a"),Var("x")))),Const(2)) *)

(* We weren't told IFTE and Lambda till then *)

(* 
Other things that I have implemented are Xor , Max, Min, Var 15 examples given in the code itself
*)
(* Automate the checking? *)
