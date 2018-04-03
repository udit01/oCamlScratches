(* 
Author -> Udit Jain
Entry Number -> 2016CS10327 

PROBLEM STATEMENT 
Consider a tiny language consisting of expressions that are
e ::= x | \x.e_1 | (e_1 e_2)
where \x.e_1 is to be read as "\lambda x. e_1"

{
In addition, to make things interesting, you can add the booleans T and F, and an if_then_else expression.  And tuples.
You can also introduce the natural numbers, addition (perhaps multiplication) and comparisons (=, >)
}

For the language you take, you should design and implement (in OCaml) the following abstract machines
1.  The Krivine Machine (in closure form), that implements Call-by-Name semantics.
For this you need to consider Closures as a pair of a Table and an expression, where a Table is a partial function from variables to Answers (including value closures).
2. The SECD machine that implements Call-by-Value semantics.
For this you need value closures in the set of answers. 
You also need to implement the compile function.
Extra credit for additional features.
Most importantly, you need to provide inputs that demonstrate that your implementations of the two machines run correctly.

*)

(* EXAMPLES ARE PROVIDES AT THE END *)
type variable = Var of string 

type exp =  true | false
            | C of int (*Const of int*)
            | V of variable (*variable is arbitary you could change this and gamma*)
            | Lambda of variable * exp
            | Apply of exp * exp
            
            (* LOCAL DEFINITIONS 
            | Not of exp
            | Or of exp*exp
            | And of exp*exp
            | Xor of exp*exp
            | Impl of exp*exp
            | Const of int 
            | Mod of exp
            | Add of exp*exp       
            | Sub of exp*exp       
            | Mul of exp*exp       
            | Div of exp*exp       
            | Pow of exp*exp
            | Max of exp*exp
            | Min of exp*exp
            | EqI of exp*exp
            | Gt of exp*exp
            | Lt of exp*exp
            | Gte of exp*exp
            | Lte of exp*exp
            | Tuple of (exp list)
            | Proj of int * (exp) *)

(* Answer of type value closure  *)

(* 
Closure is Table * Expression
Table is Variable -> Closure 
*)

(* type closure = Cl of table * exp
  and table = (variable, closure) Hashtbl.t ;;


type closure = Cl of table * exp
and table = variable -> closure ;; *)


type closure = Null |  Cl of table * exp
and table = (variable * closure) list ;;

type answer = VClosure of table * exp 
              (* | Tuple of answer list etc *)

let rec lookup (gamma:table) ((Var s):variable) : closure = match gamma with
      [] -> Null 
      | (Var str , cl)::tl -> if (s = str) then (cl) else (lookup tl (Var s))
      ;;
                  
(* Make an unpack function *)

exception NullClosure
exception ExpectedClosureOnStack
exception MalformedExp
let rec execute ((clos:closure), (stack:closure list)) = match (clos,stack) with
(* base case ? *)
          (Null, stack) -> raise NullClosure
        | ( Cl (gamma , true ) , stack ) -> VClosure(gamma,true)
        | ( Cl (gamma , false) , stack ) -> VClosure(gamma,false)
        | ( Cl (gamma , C i  ) , stack ) -> VClosure(gamma, C i)  
        | ( Cl (gamma , V v  ) , stack ) -> execute ( lookup gamma v , stack ) 
        | ( Cl (gamma', Lambda(v, exp')) , (Cl(gamma,exp))::stack ) -> execute ( Cl ( (v, Cl(gamma,exp))::gamma' ,  exp' ) , stack ) 
        (* | ( Cl (gamma', Lambda(v, exp')) , [] ) -> raise ExpectedClosureOnStack *)
        | ( Cl (gamma , Apply(exp1,exp2)) , stack) -> execute( Cl(gamma,exp1) , (Cl(gamma,exp2))::stack  ) 
        | _ -> raise MalformedExp
