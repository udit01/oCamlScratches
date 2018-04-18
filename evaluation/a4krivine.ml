(*
 * Note: you need to change the following datatype and expressions as per your submitted code
 * Please do the changes before you come for demo.
 *)


let vc00 = execute( Cl ([ ( Var("z") , Cl ( [] , C 3 )) ], V(Var("z")) ) , [] );;
let vc01 = execute( Cl ( [] , ADD ( ADD ( C 2 , C 3 ), ADD ( C 2 , C 3 ))), [] );;
let vc02 = execute( Cl ([ ( Var("z") , Cl ( [] , C 3 )) ], ADD ( C 2 , V(Var("z")) ) ) , [] );;
let vc03 = execute( Cl ( [] , Apply ( Lambda ( Var("x") ,  ADD ( V(Var("x")) , C 1 )), C 2 )), [] );;
let vc04 = execute( Cl ( [] , Apply ( Lambda ( Var("x") ,  MUL ( V(Var("x")) , ADD ( V(Var("x")) , C 1 ))), C 2 )), [] );;
let vc05 = execute( Cl ( [] , Apply ( Lambda ( Var("x") ,  Apply ( Lambda ( Var("d") ,  MUL ( V(Var("d")) , C 2 )), C 2 )), C 2 )), [] );;
let vc06 = execute( Cl ( [] , Ifte ( GT ( C 8 , C 2 ), Apply ( Lambda ( Var("x") , DIV ( V(Var("x")) , C 2 )), C 2 ), Apply ( Lambda ( Var("x") ,  MUL ( V(Var("x")) , ADD ( V(Var("x")) , C 1 ))), C 2 ))), [] );;
let vc07 = execute( Cl ( [] , Ifte ( GT ( C 1 , C 2 ), Apply ( Lambda ( Var("x") , DIV ( V(Var("x")) , C 2 )), C 2 ), Apply ( Lambda ( Var("x") ,  MUL ( V(Var("x")) , ADD ( V(Var("x")) , C 1 ))), C 2 ))), [] );;
let vc08 = execute( Cl ( [] , Let ( Var("a") , C 2 , ADD ( V(Var("a")) , C 20 ) ) ), [] );;
let vc09 = execute( Cl ( [] , Let ( Var("a") , C 2 , ADD ( V(Var("a")) , C 20 ) ) ), [] );;
let vc10 = execute( Cl ( [] , Proj ( 2 , Tuple( 3, [ C 1 ; C 2 ; C 3 ] ) ) ), [] );;(* Check 2 or 1 in above projection according to index (0 indexed) or kth position(1 indexed) *)
let vc11 = execute( Cl ( [] , Apply ( Lambda ( Var("x") ,  Let ( Var("a") , C 2 , ADD ( V(Var("a")) , V(Var("x")) ))) , C 2 )) , [] );;
(* Made the Def expressions seperately. *)
unpack vc00 ;;
unpack vc01 ;;
unpack vc02 ;;
unpack vc03 ;;
unpack vc04 ;;
unpack vc05 ;;
unpack vc06 ;;
unpack vc07 ;;
unpack vc08 ;;
unpack vc09 ;;
unpack vc10 ;;
unpack vc11 ;;