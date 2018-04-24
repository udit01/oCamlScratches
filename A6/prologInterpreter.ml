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

open Printf ;;
open Unix ;;

type variable = Var of string ;;
type symbol = Sym of string;;
type term = V of variable | Cons of string | Node of atom
and atom = Atom of symbol * (term list);;
type goal = atom list;;
type clause = Clause of atom * (atom list);;
(* Head and body implicit, head always there but not  body *)
type program = clause list;;
type substitution = (variable * term) list ;;
type 'a answer = True of 'a | False;;

let rec foldl f e l = match l with
	  [] -> e
  | x::xs -> foldl f (f(x,e)) xs;;

let rec vars_term t = match t with
	  V x -> [x]
  | Node(atom) ->vars_atom atom 
  | Cons(s) -> []
  
and  vars_atom atom = match atom with 
        Atom(sym, []) -> []
        |Atom(sym, l) ->  let rec list_union (x,y) = match x with
                [] -> y
                | x::xs -> if (List.mem x y) then list_union (xs, y) else x::(list_union (xs, y)) in
  			foldl list_union [] (List.map vars_term l)

let rec substitute_term (s:substitution) (x:term) : term = 
  match x with
        Cons c -> Cons c
	      |V v -> let rec find v s = match s with
                  [] -> V v
                  | (a,b)::xs -> if (v = a) then b else (find v xs )
                  in
                find v s
        | Node(atom) -> Node(substitute_atom s atom)

and  substitute_atom (s:substitution) (a:atom) : atom = 
  match a with 
    Atom(sym, []) -> Atom(sym, [])
    |Atom(sym, l) -> Atom(sym, List.map (substitute_term s) l) 
    ;;

let composition (s1:substitution) (s2:substitution) : substitution = 
  let s1' (a,b) = (a, substitute_term s2 b) in
  let s1s2 = List.map s1' s1 in 
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


(* This function is for termianl Input-Output by ; and . keys *)
let get1char () =
    let terminal_io_ = Unix.tcgetattr Unix.stdin in
    let () =
        Unix.tcsetattr Unix.stdin Unix.TCSADRAIN
            { terminal_io_ with Unix.c_icanon = false } in
    let res = input_char Pervasives.stdin in
    Unix.tcsetattr Unix.stdin Unix.TCSADRAIN terminal_io_;
    res 
;;
let rec continue_answer () = let () = flush Pervasives.stdout in let ch = get1char() in let () = Printf.printf "\n" in let () = flush Pervasives.stdout in if ch = ';' then true else if ch = '.' then false else
   let () = Printf.printf "Unrecognized option.\nEnter \';\' to continue backtracking \nor enter \'.\' to terminate." in let () = flush Pervasives.stdout in continue_answer()
;;


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
  				let rec fold_subst sigma t u = match (t,u) with
                  ([],[]) -> sigma
                | (t1::tr, u1::ur) -> fold_subst (composition sigma (mgu (substitute_term sigma t1) (substitute_term sigma u1))) tr ur
                | _ -> raise Error in
                (* Above error shouldn't come *)
          fold_subst [] t' u'
          else raise NOT_UNIFIABLE
  | _ -> raise NOT_UNIFIABLE (*Of the type Cons, Atom*)

and  mgu_atom (Atom (sy1,lst1)) (Atom (sy2,lst2) ) =  if (sy1 <> sy2) || ((List.length lst1) <> (List.length lst2)) then raise NOT_UNIFIABLE
          else 	let rec fold sigma t u = match (t,u) with
                  ([],[]) -> sigma
                | (t1::tr, u1::ur) -> fold (composition sigma (mgu (substitute_term sigma t1) (substitute_term sigma u1))) tr ur
                | _ -> raise Error in
          fold [] lst1 lst2
;;

let rec search_clauses func = function
  [] -> (* Printf.printf "failed search_clauses"; flush Pervasives.stdout; *) False
| hd::tl -> (
              (* [Cons "nil"; Var "_A"; Var "_A"] *)
                match (func hd) with
                  False -> search_clauses func tl
                | True ans -> (True ans)
              )
;;

(*
  make_new_program changes the variable names in the prog to _+<var_name>
  This is done to ensure that variables names do not mix during unification
*)
let rec make_new_program program = function
  [] -> List.rev program
| cl :: tl -> make_new_program ((make_new_clause cl)::program) tl
and make_new_clause = function
|Clause(atom, atoml) -> Clause (make_new_atom atom, (List.map make_new_atom atoml) )
and make_new_atom (Atom (sy,term_list)) = (Atom (sy, List.map make_new_term term_list) )
and make_new_term = function
| V (Var s) ->V (Var (s^"_"))
| Cons s -> Cons s
| Node at -> Node (make_new_atom at)
;;

let rec string_of_atom (Atom ((Sym sy),trm_list)) = let base = Printf.sprintf "%s( " sy in
Printf.sprintf "%s)" (List.fold_left (fun a b -> Printf.sprintf "%s%s, " a (string_of_term b) ) base trm_list)

and string_of_term trm = match trm with
  V (Var str) -> Printf.sprintf "V(Var(%s))" str
| Cons str -> Printf.sprintf "Cons(%s)" str
| Node atm -> Printf.sprintf "(%s)" (string_of_atom atm)
;;

(* let print_term trm = Printf.printf "%s " (string_of_term trm);; *)
let rec print_unifier unif = match unif with 
      [] -> Printf.printf " , "
      |(Var str, term)::tl -> ( Printf.printf " |  Var(%s) -> %s " str (string_of_term term) ) ; print_unifier tl   


let rec interpret (current_substitution:substitution) program goals = match goals with
  [] ->                 print_unifier current_substitution;
                          (* Printf.printf "print_unifier here" ; *)
                          flush Pervasives.stdout;
                           if (continue_answer () ) then False 
                           else True current_substitution
| (Atom (Sym("Cut"),[]) ) :: g_tail -> (
                          (* And don't come back !!  *)
                        (* Cut unifies with everyone *)
                        (try
                          (* let unif2 = (composition (mgu (subst unifier t1) (subst unifier t2)) unifier) *)
                           (interpret current_substitution program g_tail)
                        with
                          NOT_UNIFIABLE -> False) ; False 
                          (* False after *)
                        )

| (Atom (Sym("Fail"),[]) ) :: gtail -> (False)
| g_head :: g_tail ->  let new_prog = (make_new_program [] program) in
            search_clauses (fun clause -> try (interpret_clause current_substitution new_prog goals clause) with NOT_UNIFIABLE -> False ) new_prog

and interpret_clause (current_substitution:substitution) program (ghead::gtail) clause = match clause with
| Clause (atm,atm_list) -> let new_unifier = (composition (mgu_atom (substitute_atom current_substitution atm) (substitute_atom current_substitution ghead)) current_substitution ) 
                                in
                            interpret new_unifier program (atm_list @ gtail)
;;

let start = [Clause ( (Atom(Sym "start",[V (Var "Z")])), [] ) ]                
let p1 = start @ [ Clause((Atom(Sym "foo" , [ V (Var "X") ] ) ) , [( Atom(Sym "start" , [ V (Var "X") ] ) )  ]) ] ;;
let g1 = ( Atom(Sym "foo", [V (Var "Y")]) ) ;;
let g2 = ( Atom(Sym "start", [V (Var "X")]) ) ;;
let g3 = ( Atom(Sym "start", []) ) ;;

interpret []  p1 [g1]
;;

let p4 = [ 
      Clause(Atom(Sym "edge" , [Cons "a" ; Cons "b"]),[]) ; 
      Clause(Atom(Sym "edge" , [Cons "b" ; Cons "c"]),[]) ;
      Clause(Atom(Sym "edge" , [Cons "c" ; Cons "a"]),[]) ; 
      Clause(Atom(Sym "path" , [V (Var "S") ; V (Var "S")]),[]) ; 
      Clause( Atom(Sym "path" , [V (Var "S") ; V (Var "D")]) , [ (Atom(Sym "edge" , [V (Var "S") ; V (Var "Z")])) ; (Atom(Sym "path" , [V (Var "Z") ; V (Var "D")]))  ] ) 
      ]

let g4 = ( Atom(Sym "path" , [Cons "a" ; V (Var "X")]) ) ;;
let g5 = ( Atom(Sym "path" , [Cons "a" ; Cons "b" ]) ) ;;


interpret []  p4 [g4]
;;

interpret []  p4 [g5]
;;
