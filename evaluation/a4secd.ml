(*
 * Note: you need to change the following datatype and expressions as per your submitted code
 * Please do the changes before you come for demo, 
 *)

execute( [], [],  compile( Proj( 2, Tuple([ Const 12 ; Const 121 ; Const 33 ]) ) ), [] ) ;;

(* execute( [ Let ( Para([ Assgn (Var("a"), Const 1 ), Assgn (Var("b"), Const 2 ), Assgn (Var("c"), Const 3 )]), Add ( Add ( V(Var("a")) , V(Var("b")) ), Mul ( V(Var("c")) , Const 2 ))) , Mul ( Const 2 , Const 3 ) ] ) ;; *)

execute( [], [ ( Var("a"), AInt 1 );(Var("b"), AInt 2 ) ; (Var("c"), AInt 3 ) ] ,  compile(Add ( Add ( V(Var("a")) , V(Var("b")) ), Mul ( V(Var("c")) , Const 2 ))) @ compile(Mul ( Const 2 , Const 3 )) , [] ) ;;


execute( [], [], compile( Ifte ( Gt ( Const 4 , Const 2 ), Add ( Const 1 , Const 3 ), Sub ( Const 1 , Const 3 ))) , [] ) ;;

execute( [], [(Var("f"),ABool(false));(Var("a"), AInt 1); (Var("b"), AInt 2 ); (Var("c"), AInt 3 ) ] ,  compile(Add ( Add (V (Var("a")),V (Var("b"))), Mul (V (Var("c")), Const 2 ))) @ compile( Mul ( Const 2 , Const 3 )) , [] ) ;;

execute( [], [],  compile( Apply ( L(Lambda( Var("x"), Add (V (Var("x")), Const 1 ))) , Const 2 )) , [] ) ;;

execute( [], [] , compile ( Apply ( L(Lambda (Var("x"), Mul (V (Var("x")), Add (V (Var("x")), Const 1 )))), Const 2 )), [] ) ;;

execute( [], [] , compile( Apply ( L (Lambda (Var("x"), Apply ( L(Lambda(Var("d"), Mul(V (Var "d") , Const 2) )) , Const 2 ))) , Const 2 )) , [] ) ;;
(* ^ parantheses wrong *)

execute( [], [ (Var "a" , AInt 1) ],  compile(Apply ( L (Lambda (Var("x"), Add (V(Var("x")), Const 1 ))), V(Var("a"))) )@compile(Add (V (Var("a")), Const 1 )) , [] );;



