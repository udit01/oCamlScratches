(* 
Author -> Udit Jain
Entry Number -> 2016CS10327 
*)

(* EXAMPLES ARE PROVIDED AT THE END *)

open List
type symbol = S of string
type variable = Var of string

type sym = Pair of symbol*int 
type signat = sym list

type term = V of variable | Node of symbol*(term list) | None


(* MY checker doesn't allow repeated symbols *)
(* I have done hd::l instead of l@[hd] which reverses the order but makes the code faster in case of long signatures *)

let check_sig si = 
    let rec chk s l = match s with 
        [] -> (true,l)
        |(hd::tl) -> (if (mem hd l) then ((false,l)) else (match hd with
                                                            Pair (S str,i) -> if ((i>=0)) then (chk tl (hd::l)) else ((false,l))
                                                                ) )  in
    match (chk si []) with (a,b) -> a ;;

exception BadSignature
exception SymbolNotFound
(* Returns the arity of that particular symbol from the signature *)
let  get_arity signat sym = 
    let rec getArr signat sym = match signat with
            [] -> raise SymbolNotFound
            | hd::tl -> (match hd with 
                            Pair(s,i) -> (if (s = sym) then (i) else (getArr tl sym))
                            (* |  _ -> raise BadSignature) *)
                        )
             in
    getArr signat sym

exception ArityLengthClash
exception BadOrEmptyTerm

let and_l b1 b2 = (b1 && b2)
(* checks but raises exception if wrong instead of returning false *)
let rec wfterm signat term = match term with 
    (* None is a good empty term just a placeholder right ? *)
        (V (Var str)) -> true
        | Node ( sy , l) -> (if  ((length l) <> ( get_arity signat sy) ) then ((raise ArityLengthClash)) 
                                else ( fold_left and_l (true) (map (wfterm signat) l )  ) ) 
        | _ -> ((raise BadOrEmptyTerm)) 

let ht term = 
    let rec hgt h t = (match t with 
        None -> 0
        |(V (Var str)) -> 0
        | Node (sym, l) -> 1 + (fold_left max (0) (map (hgt h) l))
        )
    in
    hgt 0 term 

let add_l i1 i2 = (i1 + i2)
let size term = 
    let rec siz s t = (match t with 
        None -> 0
        | (V (Var str))-> s
        | Node (sym,l) -> 1 + (fold_left (add_l) (0) (map (siz s) l) )
        )
    in
    siz 1 term


(* vars will return the list of variables in the term *)
let cmp a b = if (a=b) then (0) else (1);;
let vars term = 
    let rec vrs vl t = (match t with 
        None -> []
        |(V v)-> v::vl
        | Node (sym,l) ->  ( concat (map (vrs []) l) )
        )
    in
    sort_uniq cmp (vrs [] term)

exception SubstitutionNotFound
exception BadSubst
(* find subs returns the corresponding term from the list of term -> term substitutions *)
let findSubs v2tlist v = 
    let rec fs v2tlist v = match v2tlist with
            [] -> (V v) 
            (* ^ return the same (term of) variable if not found *)
            | hd::tl -> (match hd with 
                            (V var, t) -> (if (var = v) then (t) else (fs tl v))
                            | _ -> raise BadSubst
                        )
             in
    fs v2tlist v

(* term to substituted term *)
let substl v2tl term = 
    let rec subs v2tl t = (match t with 
        None -> None
        |(V v)-> (findSubs v2tl v)
        | Node (sym,l) -> Node( sym ,( map (subs v2tl) l ))
        )
    in
    subs v2tl term

exception MalformedList
exception NOT_UNIFIABLE
exception InvalidComposition
exception NOT_COMPOSABLE

let rec findMatch vt sbl = match sbl with
        [] -> None
        | (v,s)::tl -> (if (v=vt) then (s) else (findMatch vt tl) )  

(* ORDER MATTERS *)
(* implemented below of s1 O s2 ie s1(s2(term))  or s2s1 in notation*)
let rec compose s2 s1 = match s1 with
        [] -> s2
        | (V var , t )::tl -> (let m = findMatch (V var) s2  in
                                if(m = None) then (compose (s2@[(V var,t)]) tl )
                                else if (m = t) then (compose (s2) tl )
                                else (raise NOT_COMPOSABLE) )
        | _ -> raise InvalidComposition                        


let rec mgu signat (t,u) = match (t,u) with
    (* (V v, V v) -> [] *)
    (V v1, V v2) -> (if (v1=v2) then([]) 
                        else ([(V v1,V v2)]))
    (* What about Node, Var case ?  *)
    | (V v, Node (sym,l)) -> (if ((get_arity signat sym)=0) then ([(V v,Node(sym,l))] ) 
                                else ( if(mem v (vars (Node(sym,l)) ) ) then (raise NOT_UNIFIABLE)
                                        else ([V v,Node(sym,l)]) ) )
    | (Node (sym,l), V v) -> (if ((get_arity signat sym)=0) then ([(V v,Node(sym,l))] ) 
                                else ( if(mem v (vars (Node(sym,l)) ) ) then (raise NOT_UNIFIABLE)
                                        else ([V v,Node(sym,l)]) ) )
    | (Node(sym1,l1),Node(sym2,l2)) -> (if(sym1 <> sym2) then (raise NOT_UNIFIABLE)
                                        else  ( let rec iter s (l1,l2) = match (l1,l2) with
                                                        ([],[]) -> s
                                                        | (h1::t1,h2::t2) -> iter (compose s  (mgu signat ((substl s h1),(substl s h2)) )  )   (t1,t2)
                                                        | _ -> raise MalformedList
                                                    in
                                                (iter [] (l1,l2)) ) )
    | _ -> raise NOT_UNIFIABLE
    (* in
    mgu signature (t,u) *)


let rec subst s x = 
    match x with
        V v -> let rec find (V v) s = match s with
                [] -> V v
                | (a,b)::xs -> if ((V v) = a) then b else find (V v) xs in
                find (V v) s
    | Node(sym, l) -> if (l = []) then Node(sym, l)
                else let subst1 x = subst s x in
                let l' = map subst1 l in 
                Node(sym, l')
    | _ -> x;;
      
exception NOT_UNIFIABLE;;
let rec mgut t u  = 
    match (t, u) with
        (V x, V y) -> if (x = y) then [] else [(V x, V y)]
    | (V x, Node(sym, [])) -> [(V x, Node(sym, []))]
    | (Node(sym, []), V x) -> [(V x, Node(sym, []))]
    | (V x, Node(sym, l)) -> if (List.mem x (vars (Node(sym, l)))) then raise NOT_UNIFIABLE 
                            else [(V x, Node(sym, l))]
    | (Node(sym, l), V x) -> if (List.mem x (vars (Node(sym, l)))) then raise NOT_UNIFIABLE
                            else [(V x, Node(sym, l))]
    | (Node(sym, []), Node(sym', [])) -> if (sym = sym') then [] else raise NOT_UNIFIABLE
    | (Node(sym, t'), Node(sym', u')) -> if (List.length t' = List.length u' && sym = sym') then
                    let rec fold sigma t u = match (t,u) with
                    ([],[]) -> sigma
                | (hl::tl, hr::tr) -> fold (compose sigma (mgut (subst sigma hl) (subst sigma hr))) tl tr
                | _ -> raise NOT_UNIFIABLE in
            fold [] t' u'
            else raise NOT_UNIFIABLE
    | _ -> raise NOT_UNIFIABLE;; 
    
(* let sig1 = [Pair(S "+",2); Pair(S "-",2) ; Pair(S "*",2) ; Pair(S "||",1) ; Pair(S "#", 4)] *)
let sig1 = [Pair(S "Unit",0);Pair(S "+",2); Pair(S "-",2) ; Pair(S "*",2) ; Pair(S "||",1) ; Pair(S "#", 4) ; Pair( S "@" ,2 ); Pair (S "0", 0);Pair (S "1", 0) ];;
let sig2  = [Pair (S "+", 2); Pair (S "+", 1); Pair  (S "1", -1)];;

check_sig sig1;;
(* bool = true *)
check_sig sig2;;
(* bool = false *)

(* substitution below *)
let var2termlist1 = [(V (Var "a") , Node (S "Unit",[])) ]

(* basic checking terms for t0 to t6 *)
let t0 = Node (S "Unit",[])
let t1 = V (Var "a");;
let t2 = Node ( S "||" ,[t1]);;
let t3 = Node (S "#",[t2;t2;t1;t0]);;
let t4 = substl var2termlist1 t3;;
let t5 = V (Var "b");;
let t6 = Node (S "@" , [t5;t1]);;
let t7 = Node(S "+", [V (Var "x"); Node(S "+", [Node(S "1", [])])]);; (* invalid term *)

(* wfterm sig1 t7;; *)

let list1 = [t0;t1;t2;t3;t4;t5;t6];;

let u x = ()
let rec checker signat i l = match l with
        [] -> (Printf.printf "Checking done for %d values.\n" i ) 
        | hd::tl -> ( ( u ( (wfterm signat  hd) = true ) ) ;
                      u (ht hd);u (size hd);u ( vars hd);u (substl var2termlist1 hd );u (mgu signat (hd,hd)) ;(Printf.printf "Success for: %d\n" i ) ; checker signat (i+1) tl  )
        (* | _ ->    (Printf.printf "Error in positioning of lables and input data : %d\n" i )  ;;           *)
;;

checker sig1 0 list1;;

(* Other cases are wfterms , height, size, vars, substitution , composition, mgu of interlinked, some interesting mgu's *)
(* MGU cases are:- *)
(* advanced test cases for testing Mgu and compose , all terms are well formed *)
let vx = V (Var "x");; (* variable x *)
let vz = V (Var "z");;
let vy = V (Var "y");;

let ter1 = Node(S "+" , [t1;t5]);;
let ter2 = Node(S "+" , [t5;t1] );;
let ter3 = Node(S "-" , [t5;t1] );;
let ter4 = Node(S "+" , [vx;t0]);;
let ter5 = Node(S "+" , [t1;vx]);;
let ter6 = Node(S "+" , [vx;t0]);;
let ter7 = Node(S "+" , [t2;vx]);;
let ter8 = Node(S "+", [vx; Node(S "1", [])]);;
let ter9 = Node(S "+", [Node(S "+", [vx;vy]); Node(S "-", [vx; vy])]);;
let ter10 = Node(S "+", [Node(S "-", [Node(S "1", []); vx]); Node(S "+", [vx; Node(S "0", [])])]);;
let ter11 = Node(S "+", [Node(S "-", [Node(S "1", []); Node(S "0", [])]); Node(S "+", [vz;vx])]);;
let ter12 = Node(S "+", [Node(S "-", [vx; Node(S "0", [])]);vy]);;
let ter13 = Node(S "+", [vz; Node(S "-", [Node(S "1", []);vx])]);;


mgu sig1 (vx,t5);;
(* (term * term) list = [(V (Var "x"), V (Var "b"))] *)
mgu sig1 (t5,vx);;
(* (term * term) list = [(V (Var "b"), V (Var "x"))] *)
mgu sig1 (t6,vx);;
(* [(V (Var "x"), Node (S "@", [V (Var "b"); V (Var "a")]))] *)
mgu sig1 (vx,t6);;
(* [(V (Var "x"), Node (S "@", [V (Var "b"); V (Var "a")]))] *)
mgu sig1 (ter4,ter5);;
(* [(V (Var "x"), V (Var "a")); (V (Var "a"), Node (S "Unit", []))] *)
mgu sig1 ( ter8 , vz);;
(* [(V (Var "z"), Node (S "+", [V (Var "x"); Node (S "1", [])]))] *)
mgu sig1 ( ter8 , vy);;
(* [(V (Var "y"), Node (S "+", [V (Var "x"); Node (S "1", [])]))] *)
mgu sig1 ( ter9 , vz);;
(* [(V (Var "z"),
  Node (S "+",
   [Node (S "+", [V (Var "x"); V (Var "y")]);
    Node (S "-", [V (Var "x"); V (Var "y")])]))] *)
mgu sig1 ( vz , vy);;
 (* [(V (Var "z"), V (Var "y"))] *)
mgu sig1 ( ter10 , ter11);;
(* [(V (Var "x"), Node (S "0", [])); (V (Var "z"), Node (S "0", []))] *)
mgu sig1 ( ter12 , ter13);;
(* [(V (Var "z"), Node (S "-", [V (Var "x"); Node (S "0", [])]));
 (V (Var "y"), Node (S "-", [Node (S "1", []); V (Var "x")]))] *)

(* 
(* Not unifiable examples at last *)
 mgu sig1 (ter6,ter7);;
(* Exception: NOT_UNIFIABLE. *)

mgu sig1 ( ter8 , ter9);;
(* Exception: NOT_UNIFIABLE *)

mgu sig1 ( ter9 , vy);;
(* Exception: NOT_UNIFIABLE.  *)
*)