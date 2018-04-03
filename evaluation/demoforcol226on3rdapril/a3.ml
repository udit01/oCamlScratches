let sig1 = [Pair (S "X",0);Pair (S "Y",0);Pair (S "f",1);Pair (S "g",2);Pair (S "h",3);Pair (S "*",2)];;
let sig2 = [Pair (S "X",0);Pair (S "Y",0);Pair (S "Z",0);Pair (S "f",1);Pair (S "g",2);Pair (S "f",3);Pair (S "*",2)];;
let sig3 = [Pair (S "f",1)];;
let sig4 = [Pair (S "X",0);Pair (S "Y",0);Pair (S "Z",0)];;
let sig5 = [Pair (S "$",2); Pair (S "g",2) ; Pair(S "*",2); Pair(S "2",0); Pair(S "4", 0) ];;
let sig6 = [Pair (S "*",2); Pair (S "g",2) ]

let term1 = (Node (S "f",[V (Var "X")]));;
let term2 = (Node (S "g",[V (Var "X");Node (S "h",[Node (S "f",[V (Var "X")]);V (Var "Y")])]));;
let term3 = (Node (S "g",[V (Var "X");Node (S "*",[V (Var "Y");Node (S "*",[V (Var "X");V (Var "Y")])])]));;
let term4 = (Node (S "g",[V (Var "X");Node (S "*",[V (Var "Y");V (Var "X")])]));;
let term5 = (Node (S "g",[V (Var "Z");Node (S "*",[V (Var "X");V (Var "Z")])]));;
let term6 = (Node (S "g",[V (Var "Z");Node (S "g",[V (Var "X");V (Var "Z")])]));;
let term7 = (V (Var "X"));;
let term8 = (Node (S "K",[]));;
let term9 = (Node (S "X",[]));;
let term10 = (Node (S "g",[V (Var "X");Node (S "h",[Node (S "f",[V (Var "X")]);V (Var "Y");Node (S "X",[])])]));;
let term11 = (Node (S "g",[V (Var "X");Node (S "h",[Node (S "f",[V (Var "X")]);V (Var "Y");Node (S "f",[V (Var "X")])])]));;
let term12 = (Node (S "g",[V (Var "Z");Node (S "*",[V (Var "Z");Node (S "*",[V (Var "X");V (Var "Y")])])]));;
let term13 = (Node (S "$",[V (Var "P");V (Var "Q")]));;
let term14 = (Node (S "$",[Node (S "2",[]); Node (S "4",[])]));;
let term15 = (Node (S "$",[Node (S "2",[]); Node (S "3",[])]));;

Printf.printf "(1)check_sig sig1 : %B\n" (check_sig sig1);;
Printf.printf "(2)check_sig sig2 : %B\n" (check_sig sig2);;
Printf.printf "(3)check_sig sig3 : %B\n" (check_sig sig3);;
Printf.printf "(4)check_sig sig4 : %B\n\n" (check_sig sig4);;

Printf.printf "(5)wfterm sig1 term1 : %B\n" (wfterm sig1 term1);;
Printf.printf "(6)wfterm sig1 term2 : %B\n" (wfterm sig1 term2);;
Printf.printf "(7)wfterm sig4 term7 : %B\n" (wfterm sig4 term7);;
(* Printf.printf "(8)wfterm sig4 term8 : %B\n" (wfterm sig4 term8);; *)
Printf.printf "(9)wfterm sig4 term9 : %B\n\n" (wfterm sig4 term9);;

Printf.printf "(10)ht term9 : %d\n" (ht term9);;
Printf.printf "(11)ht term7 : %d\n" (ht term7);;
Printf.printf "(12)ht term4 : %d\n" (ht term4);;
Printf.printf "(13)ht term10 : %d\n" (ht term10);;
Printf.printf "(14)ht term11 : %d\n\n" (ht term11);;

Printf.printf "(15)size term9 : %d\n" (size term9);;
Printf.printf "(16)size term7 : %d\n" (size term7);;
Printf.printf "(17)size term4 : %d\n" (size term4);;
Printf.printf "(1zl8)size term10 : %d\n" (size term10);;
Printf.printf "(19)size term11 : %d\n\n" (size term11);;

Printf.printf "(20)vars term9 : ";; (vars term9);; Printf.printf("\n");;
Printf.printf "(21)vars term7 : ";; (vars term7);; Printf.printf("\n");;
Printf.printf "(22)vars term4 : ";; (vars term4);; Printf.printf("\n");;
Printf.printf "(23)vars term10 : ";; (vars term10);; Printf.printf("\n");;
Printf.printf "(24)vars term11 : ";; (vars term11);; Printf.printf("\n\n");;


Printf.printf "(31)mgu term14 term13 : ";; (mgu sig5 (term14, term13));; Printf.printf("\n");;
Printf.printf "(33)mgu term3  term12 : ";; ((mgu sig5 (term3, term12)));; Printf.printf("\n");;
Printf.printf "(34)mgu term12 term3  : ";; ((mgu sig5 (term12, term3)));; Printf.printf("\n\n");;

Printf.printf "(33.1)subst term12 (mgu term3 term12)  : ";; (substl  (mgu sig5 (term3, term12))) term12;; Printf.printf("\n");;
Printf.printf "(33.2)subst term3  (mgu term3 term12)  : ";; (substl  (mgu sig5 (term3, term12))) term3;; Printf.printf("\n\n");;

Printf.printf "(34.1)subst term12 (mgu term12 term3)  : ";; (substl  (mgu sig6 (term12, term3))) term12;; Printf.printf("\n");;
Printf.printf "(34.2)subst term3  (mgu term12 term3)  : ";; (substl  (mgu sig6 (term3, term12))) term3;; Printf.printf("\n\n");;
