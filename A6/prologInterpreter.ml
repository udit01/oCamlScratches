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

type atom = A of (int) * (term list) ;;
(* ^ Predicate sybol or 'constructor' of Prolog *)

(* type fact = H of atom ;; *)
(* type rule = (H of atom) * (B of (atom list)) ;; *)

type clause = Clause of (atom) * (atom list) ;; 
(* First is automatic head and others inside body *)

type program = clause list ;;
type goal = atom list ;;

(* Define substitution function  *)
(* Define unify function  *)



let rec interpet (p:program) (g:goal) = match goal with 
        [] -> true 
        | hd::tl ->  match (getNextClause p []) with 
                        [] -> false 
                        | ph::pt ->  if ((unifyClause hd ph) = TRUE_CLAUSE) then () else (getNextClause pt [ph])


(* let rec interpret (p:program) (g:goal) = match (p, g) with 
        (p, []) -> true 
        | ( ph::pt , gh::gt) -> ( unify ph gh ) if true then  *)

