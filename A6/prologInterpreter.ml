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
        |Atom(sym, l) ->  let rec union (x,y) = match x with
                [] -> y
                | x::xs -> if (List.mem x y) then union (xs, y) else x::(union (xs, y)) in
  			foldl union [] (List.map vars_term l)

let rec subst (s:substitution) (x:term) : term = 
  match x with
        Cons c -> Cons c
	      |V v -> let rec find v s = match s with
                  [] -> V v
                  | (a,b)::xs -> if (v = a) then b else (find v xs )
                  in
                find v s
        | Node(atom) -> Node(subst_atom s atom)
        
and  subst_atom (s:substitution) (a:atom) : atom = 
  match a with 
    Atom(sym, []) -> Atom(sym, [])
    |Atom(sym, l) -> Atom(sym, List.map (subst s) l) 
    ;;

let compose (s1:substitution) (s2:substitution) : substitution = 
  let s1' (a,b) = (a, subst s2 b) in
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
                (* Above error shouldn't come *)
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

let rec search_clauses fn = function
  [] -> (* Printf.printf "failed search_clauses"; flush Pervasives.stdout; *) False
| hd::tl -> (
              (* [Cons "nil"; Var "_A"; Var "_A"] *)
                match (fn hd) with
                  False -> search_clauses fn tl
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

| (Atom (Sym("Fail"),[]) ) :: gtail -> (False)
| g_head :: g_tail ->  let new_prog = (modify_prog [] program) in
            search_clauses (fun clause -> try (interpret_clause unifier new_prog goals clause) with NOT_UNIFIABLE -> False ) new_prog

and interpret_clause (unifier:substitution) program (ghead::gtail) clause = match clause with
  (* Fact (Head atm) -> let unif2 = (compose (mgu_atm (subst_atom unifier atm) (subst_atom unifier ghead)) unifier ) in interpret unif2 program gtail *)
| Clause (atm,atm_list) -> let unif2 = (compose (mgu_atm (subst_atom unifier atm) (subst_atom unifier ghead)) unifier ) in interpret unif2 program (atm_list @ gtail)
;;

let start = [Clause ( (Atom(Sym "start",[V (Var "Z")])), [] ) ]                
let p1 = start @ [ Clause((Atom(Sym "foo" , [ V (Var "X") ] ) ) , [( Atom(Sym "start" , [ V (Var "X") ] ) )  ]) ] ;;
let g1 = ( Atom(Sym "foo", [V (Var "Y")]) ) ;;
let g2 = ( Atom(Sym "start", [V (Var "X")]) ) ;;
let g3 = ( Atom(Sym "start", []) ) ;;

interpret []  p1 [g1]
;;

