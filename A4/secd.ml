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


type exp =   true | false 
            | V of variable (*variable is arbitary you could change this and gamma*)
            | Not of exp
            | Or of exp*exp
            | And of exp*exp
            | Xor of exp*exp
            | Impl of exp*exp
            | Const of int 
            | Mod of exp*exp
            | Abs of exp
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
            | Proj of int * (exp)
            | L of lambda
            | Apply of exp * exp 
            (* Let x = e1 in e2
            Def d1 in d2
            Lambda, Apply
            Sequential, Parallel definitions 
            Local scoping rules?  *)
and lambda = Lambda of variable * exp

(* Answer of type value closure  *)
(* No diffrence between Closure and ValueClosure for SECD machine? *)
type ans = AInt of int | ABool of bool | Atuple of (ans list) | VClosure of table * lambda
  and table = (variable * ans) list;;


type opcode = TRUE 
            | FALSE 
            | LOOKUP of variable
            | NOT 
            | OR 
            | AND
            | XOR
            | IMPL
            | CONST of int
            | ABS
            | MOD
            | ADD
            | SUB
            | MUL
            | DIV
            | POW
            | MAX
            | MIN
            | EQI
            | GT
            | LT
            | GTE
            | LTE
            | PROJ of int
            | TUP of ((opcode list) list)
            | CLOSURE of variable * (opcode list)
            | RET
            | APPLY

(* type opcode =  *)
exception NotATuple

let rec compile e = match e with
        true ->  [TRUE]
        | false -> [FALSE]
        | V v -> [LOOKUP(v)]
        | Not (e1) -> (compile e1) @ [NOT]
        | Or (e1, e2) -> (compile e1) @ (compile e2) @ [OR]
        | And (e1, e2) -> (compile e1) @ (compile e2) @ [AND]
        | Xor (e1, e2) -> (compile e1) @ (compile e2) @ [XOR]
        | Impl (e1, e2) ->  (compile e1) @ (compile e2) @ [IMPL]
        | Const (n) -> [CONST (n)]
        | Mod (e1,e2) -> (compile e1)@(compile e2) @ [MOD]
        | Abs (e1) -> (compile e1) @ [ABS]
        | Add (e1,e2) -> (compile e1) @ (compile e2) @ [ADD]
        | Sub (e1,e2) -> (compile e1) @ (compile e2) @ [SUB]
        | Mul (e1,e2) -> (compile e1) @ (compile e2) @ [MUL]
        | Div (e1,e2) -> (compile e1) @ (compile e2) @ [DIV]
        | Pow (e1,e2) ->  (compile e1) @ (compile e2) @ [POW]
        | Max (e1,e2) ->  (compile e1) @ (compile e2) @ [MAX]
        | Min (e1,e2) ->  (compile e1) @ (compile e2) @ [MIN]
        | EqI (e1,e2) -> (compile e1) @ (compile e2) @ [EQI]
        | Gt (e1,e2) -> (compile e1) @ (compile e2) @ [GT]
        | Lt (e1,e2) -> (compile e1) @ (compile e2) @ [LT]
        | Gte (e1,e2) -> (compile e1) @ (compile e2) @ [GTE]
        | Lte (e1,e2) -> (compile e1) @ (compile e2) @ [LTE]
        | Tuple l -> [TUP (List.map compile l)] 
        | Proj (i,Tuple l) -> [TUP(List.map compile l)] @ [PROJ(i)]
        (* Could also have compiled only i'th of the tuple *)
        (* | Proj(i, Tuple l) -> compile (List.nth l i) *)
        | Proj (i,_) -> raise NotATuple
        | L ( Lambda (v, e) ) -> [CLOSURE(v,compile(e))] @ [RET]
        | Apply (e1, e2) -> compile(e1) @ compile(e2) @ [APPLY]
      ;;
        
(* 
Closure is Table * Expression
Table is Variable -> Closure 
*)
(* 
type closure = Cl of table * exp
  and table = (variable, closure) Hashtbl.t ;;


type closure = Cl of table * exp
and table = variable -> closure ;;

type closure = Cl of table * exp
and table = (variable * closure) list ;; *)

exception RuntimeError

(* Output of SECD is answer or full state ? *)
let rec execute (stack, gamma, opcodes, dump) = 
        match (stack, gamma, opcode, dump) with
        (a::s, g, [], d) -> a
        |(s, g, TRUE::o, d) -> execute ((ABool true)::s, g, o, d) 
        |(s, g, FALSE::o, d) -> execute ((ABool false)::s, g, o, d)
        | 


