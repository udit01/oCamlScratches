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
(* 
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
 *)
open Printf ;;
open Unix ;;

type variable = Var of string ;;
type symbol = Sym of string;;
type term = V of variable | Cons of string | Node of atom
and atom = Atom of symbol * (term list);;
type goal = atom list;;
type clause = Clause of atom * (atom list);;
type program = clause list;;
type substitution = (variable * term) list ;;
type 'a answer = True of 'a | False;;


let rec map f l = match l with
	  [] -> []
  | x::xs -> (f x)::(map f xs);;

let rec foldl f e l = match l with
	  [] -> e
  | x::xs -> foldl f (f(x,e)) xs;;

let rec vars_term t = match t with
	  V x -> [x]
  | Node(atom) ->vars_atom atom 
  | Cons(s) -> []
  
and  
vars_atom atom = match atom with 
        Atom(sym, []) -> []
        |Atom(sym, l) ->  let rec union (x,y) = match x with
                [] -> y
                | x::xs -> if (List.mem x y) then union (xs, y) else x::(union (xs, y)) in
  			foldl union [] (map vars_term l)

let rec subst (s:substitution) (x:term) : term = 
  match x with
        Cons c -> Cons c
	      |V v -> let rec find v s = match s with
                  [] -> V v
                  | (a,b)::xs -> if (v = a) then b else (find v xs )
                  in
                find v s
        | Node(atom) -> Node(subst_atom s atom)
        (* | Node(atom) -> if (l = []) then (Func(sym, l))
                else let subst1 x = subst s x in
                Func(sym, map subst1 l)
                 *)
and  subst_atom (s:substitution) (a:atom) : atom = 
  match a with 
    Atom(sym, []) -> Atom(sym, [])
    |Atom(sym, l) -> Atom(sym, List.map (subst s) l) 
    ;;

let compose (s1:substitution) (s2:substitution) : substitution = 
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



exception NOT_UNIFIABLE;;
exception Error;;

let rec mgu t u : substitution = 
  (** [val mgu : term -> term -> substitution = <fun>]  *) 
  match (t, u) with
    (Cons s1, Cons s2) -> if(s1=s2) then [] else raise NOT_UNIFIABLE
  | (V x, Cons s) -> [x, Cons s]
  | (Cons s, V x) -> [x, Cons s] 
	| (V x, V y) -> if (x = y) then [] else [(x, V y)]
  | (V x, Node(Atom(sym, []))) -> [(x, Node(Atom(sym, [])))]
  | (Node(Atom(sym, [])), V x) -> [(x, Node(Atom(sym, [])))]
  | (V x, Node(Atom(sym, l))) -> if (List.mem x (vars_atom (Atom(sym, l)))) then raise NOT_UNIFIABLE 
                           else [(x, Node(Atom(sym, l)))]
  | (Node(Atom(sym, l)), V x) -> if (List.mem x (vars_atom (Atom(sym, l)))) then raise NOT_UNIFIABLE
                           else [(x, Node(Atom(sym, l)))]
  | (Node(Atom(sym, [])), Node(Atom(sym', []))) -> if (sym = sym') then [] else raise NOT_UNIFIABLE
  | (Node(Atom(sym, t')), Node(Atom(sym', u'))) -> if (List.length t' = List.length u' && sym = sym') then
  				let rec fold sigma t u = match (t,u) with
                  ([],[]) -> sigma
                | (t1::tr, u1::ur) -> fold (compose sigma (mgu (subst sigma t1) (subst sigma u1))) tr ur
                | _ -> raise Error in
          fold [] t' u'
          else raise NOT_UNIFIABLE
  | _ -> raise NOT_UNIFIABLE (*Of the type Cons, Atom*)

and  mgu_atm (Atom (sy1,lst1)) (Atom (sy2,lst2) ) =  if (sy1 <> sy2) || ((List.length lst1) <> (List.length lst2)) then raise NOT_UNIFIABLE
          else 	let rec fold sigma t u = match (t,u) with
                  ([],[]) -> sigma
                | (t1::tr, u1::ur) -> fold (compose sigma (mgu (subst sigma t1) (subst sigma u1))) tr ur
                | _ -> raise Error in
          fold [] lst1 lst2
;;

(* 
let print_subst t1 t2 subs = let var1 = vars t1 in let var2 = vars_t var1 t2 in StringSet.fold (fun x lst -> (Var(x),(subs x))::lst ) var2 [];; 
let print_vars t = let v = vars t in StringSet.fold (fun x lst -> (Var x)::lst ) v [];;
 *)

let rec find_feasible fn = function
  [] -> (* Printf.printf "failed find_feasible"; flush Pervasives.stdout; *) False
| hd::tl -> (
              (* [Cons "nil"; Var "_A"; Var "_A"] *)
                match (fn hd) with
                  False -> find_feasible fn tl
                | True ans -> (True ans)
              )
;;

(*
  Modify_prog changes the variable names in the prog to _+<var_name>
  This is done to ensure that variables names do not mix during unification
*)

let rec modify_prog program = function
  [] -> List.rev program
| cl :: tl -> modify_prog ((modify_clause cl)::program) tl
and modify_clause = function
|Clause(atom, atoml) -> Clause (modify_atm atom, (List.map modify_atm atoml) )
and modify_atm (Atom (sy,term_list)) = (Atom (sy, List.map modify_term term_list) )
and modify_term = function
| V (Var s) ->V (Var (s^"_"))
| Cons s -> Cons s
| Node at -> Node (modify_atm at)
;;

let get1char () =
    let termio = Unix.tcgetattr Unix.stdin in
    let () =
        Unix.tcsetattr Unix.stdin Unix.TCSADRAIN
            { termio with Unix.c_icanon = false } in
    let res = input_char Pervasives.stdin in
    Unix.tcsetattr Unix.stdin Unix.TCSADRAIN termio;
    res

let rec continue_answer () = let () = flush Pervasives.stdout in let ch = get1char() in let () = Printf.printf "\n" in let () = flush Pervasives.stdout in if ch = ';' then true else if ch = '.' then false else
   let () = Printf.printf "Unrecognized option.\nEnter \';\' to continue backtracking \nor enter \'.\' to terminate." in let () = flush Pervasives.stdout in continue_answer()
;;


let rec string_of_atom (Atom ((Sym sy),trm_list)) = let base = Printf.sprintf "%s( " sy in
Printf.sprintf "%s)" (List.fold_left (fun a b -> Printf.sprintf "%s%s, " a (string_of_term b) ) base trm_list)

and string_of_term trm = match trm with
  V (Var str) -> Printf.sprintf "V(Var(%s))" str
| Cons str -> Printf.sprintf "Cons(%s)" str
| Node atm -> Printf.sprintf "(%s)" (string_of_atom atm)
;;

(* let print_term trm = Printf.printf "%s " (string_of_term trm);; *)
let rec print_ans unif = match unif with 
      [] -> Printf.printf " , "
      |(Var str, term)::tl -> ( Printf.printf " |  Var(%s) -> %s " str (string_of_term term) ) ; print_ans tl   


let rec interpret (unifier:substitution) program goals = match goals with
  [] ->                 print_ans unifier;
                          (* Printf.printf "print_ans here" ; *)
                          flush Pervasives.stdout;
                           if (continue_answer () ) then False 
                           else True unifier
(* | (Atom (Sym("Cut"),[]) ) :: g_tail -> (
                          (* And don't come back !!  *)
                        try
                          let unif2 = (compose (mgu (subst unifier t1) (subst unifier t2)) unifier)
                          in interpret  unif2 program g_tail
                        with
                          NOT_UNIFIABLE -> False
                        ) *)
| (Atom (Sym("Fail"),[]) ) :: g_tail -> (False)
| g_head :: g_tail -> 
            let new_prog = (modify_prog [] program) in
            find_feasible (fun clause -> try (interpret_clause unifier new_prog goals clause) with NOT_UNIFIABLE -> False ) new_prog

and interpret_clause (unifier:substitution) program (g_1::g_rest) clause = match clause with
  (* Fact (Head atm) -> let unif2 = (compose (mgu_atm (subst_atom unifier atm) (subst_atom unifier g_1)) unifier ) in interpret unif2 program g_rest *)
| Clause (atm,atm_list) -> let unif2 = (compose (mgu_atm (subst_atom unifier atm) (subst_atom unifier g_1)) unifier ) in interpret unif2 program (atm_list @ g_rest)
;;


let start = [Clause ( (Atom(Sym "start",[V (Var "Z")])), [] ) ]                
let p1 = start @ [ Clause((Atom(Sym "foo" , [ V (Var "X") ] ) ) , [( Atom(Sym "start" , [ V (Var "X") ] ) )  ]) ] ;;
let g1 = ( Atom(Sym "foo", [V (Var "Y")]) ) ;;
let g2 = ( Atom(Sym "start", [V (Var "X")]) ) ;;
let g3 = ( Atom(Sym "start", []) ) ;;

interpret []  p1 [g1]
;;

