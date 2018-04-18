(*
 * Note: you need to change the following datatype and expressions as per your submitted code
 * Please do the changes before you come for demo. 
 *)

execute( [ Proj( 2, Tup([ C 12 , C 121 , C 33 ]) ) ] ) ;;

(* execute( [ Let ( Para([ Assgn (Var("a"), C 1 ), Assgn (Var("b"), C 2 ), Assgn (Var("c"), C 3 )]), Add ( Add ( V(Var("a")) , V(Var("b")) ), Mul ( V(Var("c")) , C 2 ))) , Mul ( C 2 , C 3 ) ] ) ;; *)

execute( [], [ ( Var("a"), C 1 ),  (Var("b"), C 2 ),  (Var("c"), C 3 ) ] ,  compile(Add ( Add ( V(Var("a")) , V(Var("b")) ), Mul ( V(Var("c")) , C 2 ))) @ compile(Mul ( C 2 , C 3 )) , [] ) ;;

execute( [], [], compile( Let(Var "a", C 1, Let( Var "b", C 2, Let( Var "c", C 3, (Add ( Add ( V(Var("a")) , V(Var("b")) ), Mul ( V(Var("c")) , C 2 ))))))) @ compile( Mul(C 2, C 3) ), [])

execute( []. []. compile( Def([ (Var "a", C 1) ; (Var "b", C 2) ; (Var "a", C 3) ;  ]) )@ compile( Add ( Add ( V(Var("a")) , V(Var("b")) ), Mul ( V(Var("c")) , C 2 ) )) @compile(Mul(C 2, C 3)) , [])


execute( [], [] compile( Ifte ( Gt ( C 4 , C 2 ), Add ( C 1 , C 3 ), Sub ( C 1 , C 3 ))) , [] ) ;;

execute( [ Let (Dec([Para([ Assgn (Var("f"),Bool(false))]),Seq([ Assgn (Var("a"), C 1 ), Assgn (Var("b"), C 2 ), Assgn (Var("c"), C 3 )])]), Add ( Add (Var("a"),Var("b")), Mul (Var("c"), C 2 ))), Mul ( C 2 , C 3 )] ) ;;

execute( [], [],  compile( Apply ( L(Lambda( Var("x"), Add (Var("x"), C 1 ))) , C 2 ) , [] ) ;;

execute( [], [] , compile ( Apply ( L(Lambda (Var("x"), Mul (Var("x"), Add (Var("x"), C 1 )))), C 2 )), [] ) ;;

execute( [], [] , compile( Apply ( L (Lambda (Var("x"), Apply ( L(Lambda(Var("d"), Mul(V (Var "d") , C 2) )) , C 2 ))) , C 2 )) , [] ) ;;

execute( [Seq([ Assgn (Var("a"), Let (Para([ Assgn (Var("a"), C 1 )]), Apply ( Lambda (Var("x"), Add (Var("x"), C 1 )),Var("a"))))]), Add (Var("a"), C 1 )] );;



