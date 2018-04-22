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

type variable = Const of int | T of term | Var of string 
and term = V of variable | C of int | Func of (int) * (term list) ;;

type atom = Cut | Fail | A of (int) * (term list) ;;
(* ^ Predicate sybol or 'constructor' of Prolog *)

(* type fact = H of atom ;; *)
(* type rule = (H of atom) * (B of (atom list)) ;; *)

type clause = Clause of (atom) * (atom list) ;; 
(* First is automatic head and others inside body *)

type program = clause list ;;
type goal = atom list ;;

(* Define substitution function  *)
(* Define unify function  *)


(* let rec interpet (p:program) (g:goal) = match goal with 
        [] -> true 
        | hd::tl ->  match (getNextClause p []) with 
                        [] -> false 
                        | ph::pt ->  if ((unifyClause hd ph) = TRUE_CLAUSE) then () else (getNextClause pt [ph]) *)


(* let rec interpret (p:program) (g:goal) = match (p, g) with 
        (p, []) -> true 
        | ( ph::pt , gh::gt) -> ( unify ph gh ) if true then  *)


(* type goalStack = GoalSet of (goal list)*(goal list) ;;
type clauseStack = ClauseSet of (clause list) ;;
type substStack = SubstSet of ((subst list) list) ;; *)

(* ([] , [g1;g2;g3;g4]) -> ([g1] , [g2;g3;g4]) -> ([g2;g1] , [g3;g4]) -> ([g3;g2;g1] , [g4]) ->  *)
(* findUnifiableClauses is a function from (goal head) * (program) -> ( clause list) * ((substitution list) list) *)
(* let rec interpret (p:program) (gstack: goalStack list) (cstack: clauseStack list) (sstack:substStack list) =  *)
                                                    (* match ( gstack, cstack, sstack ) with 
            ( GoalSet( dgh::dgt , [] )::gst, ClauseSet( cl )::cst, ss ) ->  interpret p gst cst ss
            |( GoalSet( dgh::dgt ,gh::gt )::gst, cs, ss ) -> (match (findUnifiableClauses(gh, p)) with 
                                                        (*Nothing found from this goal, backtrack*)
                                                        ( [], sll) -> (interpet p (GoalSet(dgt, dgh::gh::gt)::gst) cs ss) 
                                                        (cl , sll) -> interpet p (GoalSet(gh::dgh::dgt, gt)::gst) (ClauseSet( cl )::cs) (SubstSet( sll )::ss) )
            |( GoalSet( dgh::dgt ,gh::gt )::gst, ClauseSet( [] )::cst, ss ) -> (match (findUnifiableClauses(gh, p)) with  *)
type subst = variable * term ;;
type gstackfull = (subst list)*(((goal)*(program)) list) ;;
type goalStack = Gs of  gstackfull;;

(* 
let rec mgu t u : substitution = 
  (** [val mgu : term -> term -> substitution = <fun>]  *) 
  match (t, u) with
	  (V x, V y) -> if (x = y) then [] else [(x, V y)]
  | (V x, Node(sym, [])) -> [(x, Node(sym, []))]
  | (Node(sym, []), V x) -> [(x, Node(sym, []))]
  | (V x, Node(sym, l)) -> if (List.mem x (vars (Node(sym, l)))) then raise NOT_UNIFIABLE 
                           else [(x, Node(sym, l))]
  | (Node(sym, l), V x) -> if (List.mem x (vars (Node(sym, l)))) then raise NOT_UNIFIABLE
                           else [(x, Node(sym, l))]
  | (Node(sym, []), Node(sym', [])) -> if (sym = sym') then [] else raise NOT_UNIFIABLE
  | (Node(sym, t'), Node(sym', u')) -> if (List.length t' = List.length u' && sym = sym') then
  				let rec fold sigma t u = match (t,u) with
                  ([],[]) -> sigma
                | (t1::tr, u1::ur) -> fold (compose sigma (mgu (subst sigma t1) (subst sigma u1))) tr ur
                | _ -> raise Error in
          fold [] t' u'
          else raise NOT_UNIFIABLE;;  *)


(* let unifyCurrier unify t1 t2 =  *)
(* Unification of atoms directly *)
let rec unify a1 a2 = match (a1, a2) with 
        ([],[]) -> (true, [])
        |(A(i, tl1), A(j, tl2)) -> if (i = j) then (List.map unify tl1 tl2) else (false, []) 
;;
let rec searchAndUnify pf (goal, prog) = match prog with 
        [] -> (false, [], [], goal, [])
        | (Clause(head, body)::tl) -> (match (unify goal head ) with 
                                        (false, sl) -> searchAndUnify pf (goal, tl)
                                        |(true, sl) -> (true, sl, body, goal, tl)
                                        )
;;

let rec interpret p (gs:gstackfull) (dump:goalStack list) = match (gs,dump) with 
                ( (csl, []) , ([])  ) -> PASS (*or done ?*)
                (* DO the below thing on pressing tab to search for more solutions *)
                (* And show the csl(current subst list) to viewrs *)
                |( (csl, []) , (Gs gsf)::d ) -> (interpret p (gsf) (d))
                (* Pop 1 from dump in case of a cut  *)
                |( (csl, ( [Cut] , prog )::gpl ) , ((Gs gsf)::d)  ) -> ( interpret p (csl,gpl) (d))
                (* In case of fail, this stack has failed  *)
                |( (csl, ( [Fail] , prog )::gpl ) , ((Gs gsf)::d)  ) -> ( interpret p (gsf) (d))
                (* In case of other clauses find and match *)
                |( (csl, ( goal, prog )::gpl ) , ((Gs gsf)::d)  ) -> (match (searchAndUnify  p (goal, prog)) with
                                                                (* sl and prog' should also be empty but i don't care , no unificatoin, no matching*)
                                                                (* But empty goal stack can also resutl from a fact See about conditions *)
                                                                (false, sl, [], g, prog' ) -> interpret (p (gsf) (d))
                                                                (* gl will full prog by their side  *)
                                                                (* Substitute will subst the whole stack and preserver the side p' *)
                                                                |(true, sl, gl, g, prog' ) -> let nsl = (compose sl csl) in 
                                                                                (interpret p ((nsl),( substitute nsl (gl@gpl))) (Gs(csl,((goal,prog')::gpl))::(Gs gsf)::d))
                                                                | _ -> FAIL
                                                                )
                (* What to do with current subst list ? *)
                
