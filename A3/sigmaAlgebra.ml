open List
(* Use HashTable later for efficiency *)
type symbol = S of string
type variable = Var of string

(* type x = (C of int) *)
type sym = Pair of symbol*int 
type signat = sym list

type term = V of variable | Node of symbol*(term list)

(* let signatr str = match str with
    S "+" -> 2 
    |S "-" -> 2
    | _ -> -1 *)

let s = [Pair(S "+",2); Pair(S "-",2) ; Pair(S "*",2) ]
(* Check signature can check for both functions and symbol lists *)
(* IDK how the one in form of functions would work but for the list, its okay, *)
    (* MY checker doesn't allow repeated symbols *)

(* I have done hd::l instead of l@[hd] which reverses the order but makes the code faster in case of long signatures *)

let check_sig si = 
    let rec chk s l = match s with 
        [] -> (true,l)
        |(hd::tl) -> (if (mem hd l) then ((false,l)) else (match hd with
                                                            Pair (S str,i) -> if ((i>=0)) then (chk tl (hd::l)) else ((false,l))
                                                                ) )  in
    chk si [] ;;

check_sig s;;

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
exception BadTerm

let and_l b1 b2 = (b1 && b2)

(* checks but raises exception if wrong instead of returning false *)
let wfterm si t = 
    (* I can check signature is well formed first here *)
    let rec checkTerm signat term = match term with 
        (V (Var str)) -> true
        | Node ( sy , l) -> (if  ((length l) <> ( get_arity signat sy) ) then ((raise ArityLengthClash)) 
                                else ( fold_left and_l (true) (map (checkTerm signat) l )  ) ) 
        (* | _ -> ((raise BadTerm))  *)
        in
    checkTerm si t

let ht term = 
    let rec hgt h t = (match t with 
        (V (Var str)) -> h
        | Node (sym, l) -> 1 + (fold_left max (0) (map (hgt h) l))
        )
    in
    hgt 0 term 

let add_l i1 i2 = (i1 + i2)
let size term = 
    let rec siz s t = (match t with 
        (V (Var str))-> s
        | Node (sym,l) -> 1 + (fold_left (add_l) (0) (map (siz s) l) )
        )
    in
    siz 0 term


(* vars will return the list of variables in the term *)
let cmp a b = 0 
let vars term = 
    let rec vrs vl t = (match t with 
        (V v)-> v::vl
        | Node (sym,l) ->  ( concat (map (vrs []) l) )
        )
    in
    sort_uniq cmp (vrs [] term)
(* Which is faster, sort_uniq inside recursive vrs or outside as now ? *)
(* I can also return count of every variables, or retrun them sorted by duplicity *)

(* What does he mean by finding a suitable represntation ? *)
(* let variable2term vr = match vr with
          Var "a" -> Node ( S "0" , [])
       | _  ->V ( Var "unknown");; *)


(* ENSURE SUBST IS EFFICIENTLY IMPLEMENTED *)
(* v2t is a function that maps variable to term *)
(* or could it be better if it's a list ? *)
(* let substf v2t term = 
    let rec subs v2t t = (match t with 
        (V v)-> (v2t v)
        | Node (sym,l) -> Node( sym ,( map (subs v2t) l ))
        )
    in
    subs v2t term *)

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
        (V v)-> (findSubs v2tl v)
        | Node (sym,l) -> Node( sym ,( map (subs v2tl) l ))
        )
    in
    subs v2tl term



exception NOT_UNIFIABLE

let mostGenUnif signature (t,u) = 
    (* Do we do tail recursion below ? *)
    (* how equivalance in exchanging t and u ? *)
    let rec mgu sig (t,u) = match (t,u) with
        (* (V v, V v) -> [] *)
         (V v1, V v2) -> (if (v1=v2) then([]) 
                            else ([(V v,V y)]))
        (* What about Node, Var case ?                     *)
        | (V v, Node (sym,l)) -> (if ((get_arity sign sym)=0) then ([(V v,Node(sym,l))] ) 
                                    else ( if(mem v (vars (Node(sym,l)) ) ) then (raise NOT_UNIFIABLE)
                                            else ([V v,Node(sym,l)]) ) )
        | (Node(sym1,l1),Node(sym2,l2)) -> (if(sym1 <> sym2) then (raise NOT_UNIFIABLE)
                                            else  ( let rec iter s (l1,l2) = match (l1,l2) with
                                                            ([],[]) -> s
                                                            | (h1::t1,h2::t2) ->   )
    in
    mgu signature (t,u)



let t1 = V (Var "a");;
let t2 = Node ( S "||" ,[t1]);;
let t3 = Node (S "#",[t2;t2;t1;t1]);;
let t4 = subst variable2term t3;;
