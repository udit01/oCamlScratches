(* Author -> Udit Jain
Entry Number -> 2016CS10327 *)

(* Assignment 6: Toy Prolog Interpreter

In this assignment, you will write a simplified version of a Prolog interpreter in OCaml.

You will first define an OCaml data type to represent the structure of a legitimate Prolog program.

Note that you only need to model the abstract syntax in this assignment.

    A program is a list of clauses. 
     A clause can either be a fact or a rule. A fact has a head but no body.  A rule has a head and a body.  
    The head is a single atomic formula.  A body is a sequence of atomic formulas.
    An atomic formula is a k-ary predicate symbol followed by a tuple of k terms.
    A term is either a variable, a constant, or a k-ary function symbol with k subterms.
    A goal is a sequence (list) of atomic formulas.

You need to take your implementation of unification to use as the parameter-passing mechanism. (Note: by pretending the predicate symbol is a function symbol, you can perform resolution of goals and program clauses). 

You need to be able to replace a chosen (sub)goal by a (possibly empty) list of subgoals, as found by applying a unifier to the body of a program clause whose head unified with the chosen (sub)goal.

You also need to develop a back-tracking strategy to explore the resolution search space, when a (sub)goal fails.

You should also include some control mechanisms, such as forced failure, and ``cut'' so that one does not backtrack to certain points in the search space. *)

(* type variable = C of int | T of term 
and term = V of variable | C of int | Func of (int) * ( term list ) ;;
type atom = Atom of (int) * ( Tuple of (term list));;
type head = A of atom ;;
type body = (A of atom) list ;; 
type fact = H of head ;;
type rule = (H of head) * (B of body) ;;
type clause = F of fact | R of rule ;;
type program = clause list ;;
type goal = atom list ;; *)

type symbol = Sym of string ;;
type variable = Const of int | T of term | Var of string 
and term = V of variable | Func of (symbol) * (term list) ;;

type atom = Cut | Fail | T of term ;;
(* ^ Predicate sybol or 'constructor' of Prolog *)

(* type fact = H of atom ;; *)
(* type rule = (H of atom) * (B of (atom list)) ;; *)

type clause = Clause of (atom) * (atom list) ;; 
(* First is automatic head and others inside body *)

type program = clause list ;;
type goal = atom ;;
type substitution = (variable * term) list;;

let rec map f l = match l with
	  [] -> []
  | x::xs -> (f x)::(map f xs);;

let rec foldl f e l = match l with
	  [] -> e
  | x::xs -> foldl f (f(x,e)) xs;;
let rec vars t = 
  (** [val vars : term -> variable list = <fun>]  *)
  match t with
	  V x -> [x]
  | Func(sym, []) -> []
  | Func(sym, l) -> let rec union (x,y) = match x with
                        [] -> y
                      | x::xs -> if (List.mem x y) then union (xs, y) else x::(union (xs, y)) in
  			foldl union [] (map vars l);; 

let rec subst (s:substitution) (x:term) = 
  match x with
	 V v -> let rec find v s = match s with
                [] -> V v
                | (a,b)::xs -> if (v = a) then b else find v xs in
                find v s
        | Func(sym, l) -> if (l = []) then (Func(sym, l))
                else let subst1 x = subst s x in
                Func(sym, map subst1 l);;

let compose (s1:substitution) (s2:substitution) : substitution = 
  (** [val compose : substitution -> substitution -> substitution = <fun>]  *)
  (* let s1 = (match bs1 with (true,l)-> l) *)
  let s1' (a,b) = (a, subst s2 b) in
  let s1s2 = map s1' s1 in 
  let rec sigma2 l = match l with
     [] -> []
   | (a,b)::xs -> let rec member a l = match l with
                    [] -> false
                  | (v,t)::xs -> if (a = v) then true else member a xs in
  if member a s1s2 then sigma2 xs else [(a,b)]@(sigma2 xs) in
  let rec rm_id l = match l with
     [] -> []
   | (a,b)::xs -> if (V a = b) then (rm_id xs) else (a,b)::(rm_id xs) in
  rm_id (s1s2 @ (sigma2 s2));;


exception InvalidArgs ;;
let rec mgu t u : (bool*substitution) = 
  (** [val mgu : term -> term -> substitution = <fun>]  *) 
  match (t, u) with
	  (V x, V y) -> if (x = y) then (true, []) else (true, [(x, V y)])
  | (V x, Func(sym, [])) -> (true, [(x, Func(sym, []))])
  | (Func(sym, []), V x) -> (true, [(x, Func(sym, []))])
  | (V x, Func(sym, l)) -> if (List.mem x (vars (Func(sym, l)))) then (false, []) 
                           else (true, [(x, Func(sym, l))])
  | (Func(sym, l), V x) -> if (List.mem x (vars (Func(sym, l)))) then (false, [])
                           else (true, [(x, Func(sym, l))])
  | (Func(sym, []), Func(sym', [])) -> if (sym = sym') then (true, []) else (false, [])
  | (Func(sym, t'), Func(sym', u')) -> if ((List.length t' = List.length u') && (sym = sym')) then
  				( 
                                let rec fold sigma t u = match (t,u) with
                                        ([],[]) -> sigma
                                        | (t1::tr, u1::ur) -> fold (compose sigma (match (mgu (subst sigma t1) (subst sigma u1)) with 
                                                                                        (true, l) -> l 
                                                                                        |(false,l) -> raise InvalidArgs )) tr ur
                                        | _ -> raise InvalidArgs 
                                        in
                                try (true, (fold [] t' u'))
                                with InvalidArgs -> (false, [])
                                )
                                else (false, [])
;; 

let unify a1 a2 = match (a1, a2) with 
        (T t1,T t2) -> mgu (t1) (t2) 
        | _ -> (false, [])
;;
let appendProgs pf goal = (goal, pf)
;;
let rec searchAndUnify pf (goal, prog) = match prog with 
        [] -> (false, [], [], goal, [])
        | (Clause(head, body)::tl) -> (match (unify goal head ) with 
                                        (false, _ ) -> searchAndUnify pf (goal, tl)
                                        |(true, sl) -> (true, sl, List.map (appendProgs pf) body, goal, tl)
                                        )
;;


(* List.map (atomify) ( List.map (subst nsl) (List.map clean (gl@gpl)) )  *)
(* from a goal* prog list i want goal * prog list ie substituted *)
exception Unsubst
let substitute substitution gpl = 
let rec substituteInst substitution gplf  goalproglist = match goalproglist with 
        (T t, prog)::tl -> substituteInst (substitution) (gplf@[ (T(subst substitution t), prog) ]) (tl)
        | _ -> raise Unsubst 
        in
        substituteInst substitution [] gpl 
;;

let clean (g,prog) = match g with 
        T t -> t 
        (* | _ ->   *)
;;
let atomify term = T term ;;

type gstackfull = (substitution)*(((goal)*(program)) list) ;;
type goalStack = Gs of  gstackfull;;

type answers = END | FAILED | MORE ;;

exception Dempty ;;
let rec interpret (p:program) (gs:gstackfull) (dump:goalStack list) = match (gs,dump) with 
                ( (csl, []) , ([])  ) -> END  (*or done ?*)
                (* DO the below thing on pressing tab to search for more solutions *)
                (* And show the csl(current subst list) to viewrs *)
                |( (csl, []) , (Gs gsf)::d ) -> 
                                                (csl) ;
                                                        (interpret p (gsf) (d))
                (* Pop 1 from dump in case of a cut  *)
                |( (csl, ( Cut , prog )::gpl ) , ((Gs gsf)::d)  ) -> ( interpret p (csl,gpl) (d))
                (* In case of fail, this stack has failed  *)
                |( (csl, ( Fail , prog )::gpl ) , ((Gs gsf)::d)  ) -> ( interpret p (gsf) (d))
                (* In case of other clauses find and match *)
                |( (csl, ( goal, prog )::gpl ) , (d)  ) -> (Printf.printf "Entered"); (match (searchAndUnify  (p) (goal, prog)) with
                                                                (* sl and prog' should also be empty but i don't care , no unificatoin, no matching*)
                                                                (* But empty goal stack can also resutl from a fact See about conditions *)
                                                                (false, _, _, _, _ ) -> (interpret p (match d with ((Gs gsf)::d2) ->gsf | _ -> raise Dempty) (d))
                                                                (* (false, sl, [], g, prog' ) -> (interpret (p (gsf) (d))) *)
                                                                (* gl will full prog by their side  *)
                                                                (* Substitute will subst the whole stack and preserver the side p' *)
                                                                |(true, sl, gl, g, prog' ) -> let nsl = (compose sl csl) in (*Change order in compose and see 2*)
                                                                                (interpret p ((nsl),( substitute nsl (gl@gpl) ) ) (Gs(csl,((goal,prog')::gpl))::d))
                                                                | _ -> FAILED
                                                                )
                
                (* |( (csl, ( goal, prog )::gpl ) , ((Gs gsf)::d)  ) -> (Printf.printf "Entered"); (match (searchAndUnify  (p) (goal, prog)) with
                                                                (* sl and prog' should also be empty but i don't care , no unificatoin, no matching*)
                                                                (* But empty goal stack can also resutl from a fact See about conditions *)
                                                                (false, _, _, _, _ ) -> (interpret p (gsf) (d))
                                                                (* (false, sl, [], g, prog' ) -> (interpret (p (gsf) (d))) *)
                                                                (* gl will full prog by their side  *)
                                                                (* Substitute will subst the whole stack and preserver the side p' *)
                                                                |(true, sl, gl, g, prog' ) -> let nsl = (compose sl csl) in (*Change order in compose and see 2*)
                                                                                (interpret p ((nsl),( substitute nsl (gl@gpl) ) ) (Gs(csl,((goal,prog')::gpl))::(Gs gsf)::d))
                                                                | _ -> FAILED
                                                                ) *)
                (* | _ -> (Printf.printf "Match Failed\n") ; FAILED *)
                (* The above statement is evil  *)
                ;;
                (* What to do with current subst list ? *)

let start = [Clause ( T (Func(Sym "start",[V (Var "Z")])), [] ) ]                
let p1 = start @ [ Clause( T ( Func(Sym "foo" , [ V (Var "X") ] ) ) , [ T ( Func(Sym "start" , [ V (Var "X") ] ) )  ]) ] ;;
let g1 = T ( Func(Sym "foo", [V (Var "VV")]) ) ;;
let g2 = T ( Func(Sym "start", [V (Var "VV")]) ) ;;
let g3 = T ( Func(Sym "start", []) ) ;;

interpret (p1) ([], [(g3,p1)] )  ([]) ;;

