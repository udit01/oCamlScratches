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
            | Eql of exp*exp
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
type ans = AInt of int 
          | ABool of bool 
          | Atuple of (ans list) 
          (* | VClosure of table * lambda  *)
          | AClosure of table * variable * (opcode list)
  and table = (variable * ans) list;;

type state = (ans list) * (table) * (opcode list)

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
            | EQL
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
        | EQL (e1,e2) -> (compile e1) @ (compile e2) @ [EQL]
        | Gt (e1,e2) -> (compile e1) @ (compile e2) @ [GT]
        | Lt (e1,e2) -> (compile e1) @ (compile e2) @ [LT]
        | Gte (e1,e2) -> (compile e1) @ (compile e2) @ [GTE]
        | Lte (e1,e2) -> (compile e1) @ (compile e2) @ [LTE]
        | Tuple l -> [TUP (List.map compile l)] 
        | Proj (i,Tuple l) -> [TUP(List.map compile l)] @ [PROJ(i)]
        (* Could also have compiled only i'th of the tuple *)
        (* | Proj(i, Tuple l) -> compile (List.nth l i) *)
        | Proj (i,_) -> raise NotATuple
        | L ( Lambda (v, e) ) -> [CLOSURE(v,compile(e)@[RET])]
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

(* Correct the below function *)
let lookup (t:table) (v:variable) : ans = 
      AInt 1;;


(* When a tuple forms do we have to evaluate all projections even if only 1 of them is required ? *)
exception RuntimeError
let executeCurry execute stack gamma dump opcodelist = execute (stack,gamma,opcodelist,dump)
(* Output of SECD is answer or full state ? *)
let rec execute ((stack: ans list), (gamma:table) , (opcodes:opcode list), dump) = 
        match (stack, gamma, opcode, dump) with
        (a::s, g, [], d) -> a
        |(s, g, TRUE::o, d) -> execute ((ABool true)::s, g, o, d) 
        |(s, g, FALSE::o, d) -> execute ((ABool false)::s, g, o, d)
        |(s, g, LOOKUP(v)::o, d) -> execute((lookup g v)::s, g, o, d)
        |((Abool b)::s, g, NOT::o, d) -> execute((Abool (not b))::s, g, o, d)
        |((Abool b1)::(Abool b2)::s, g, OR::o, d) -> execute((Abool (b1 || b2))::s, g, o, d)
        |((Abool b1)::(Abool b2)::s, g, AND::o, d) -> execute((Abool (b1 && b2))::s, g, o, d)
        |((Abool b1)::(Abool b2)::s, g, XOR::o, d) -> execute((Abool (
                                                      match (b1, b2) with 
                                                          (true,true)   -> false
                                                          |(true,false)  -> true
                                                          |(false,true)  -> true
                                                          |(false,false) -> false
                                                        ))::s, g, o, d)
        |((Abool b1)::(Abool b2)::s, g, IMPL::o, d) -> execute((Abool (
                                                      match (b1, b2) with 
                                                          (true,true)   -> true
                                                          |(true,false)  -> false
                                                          |(false,true)  -> true
                                                          |(false,false) -> true
                                                        ))::s, g, o, d)                                                        
        |(s, g, (CONST n)::o, d) -> execute((AInt n)::s, g, o, d)
        |((AInt i)::s, g, ABS::o, d) -> execute((Aint (abs i))::s, g, o, d)
        |((AInt i1)::(AInt i2)::s, g, MOD::o, d) -> execute((AInt(mod i1 i2))::s, g, o, d)
        |((AInt i1)::(AInt i2)::s, g, ADD::o, d) -> execute((AInt(i1 + i2))::s, g, o, d)
        |((AInt i1)::(AInt i2)::s, g, SUB::o, d) -> execute((AInt(i1 - i2))::s, g, o, d)
        |((AInt i1)::(AInt i2)::s, g, MUL::o, d) -> execute((AInt(i1 * i2))::s, g, o, d)
        |((AInt i1)::(AInt i2)::s, g, DIV::o, d) -> execute((AInt(i1 / i2))::s, g, o, d)
        |((AInt i1)::(AInt i2)::s, g, POW::o, d) -> execute((AInt( int_of_float( float_of_int(i1)**float_of_int(i2))))::s, g, o, d)
        |((AInt i1)::(AInt i2)::s, g, MAX::o, d) -> execute((AInt( max i1 i2 ))::s, g, o, d)
        |((AInt i1)::(AInt i2)::s, g, MIN::o, d) -> execute((AInt( min i1 i2 ))::s, g, o, d)
        |((AInt i1)::(AInt i2)::s, g, EQL::o, d) -> execute((ABool( i1 = i2 ))::s, g, o, d)
        |((AInt i1)::(AInt i2)::s, g, GT::o, d) -> execute((ABool( i1 > i2 ))::s, g, o, d)
        |((AInt i1)::(AInt i2)::s, g, LT::o, d) -> execute((ABool( i1 < i2 ))::s, g, o, d)
        |((AInt i1)::(AInt i2)::s, g, GTE::o, d) -> execute((ABool( i1 >= i2 ))::s, g, o, d)
        |((AInt i1)::(AInt i2)::s, g, LTE::o, d) -> execute((ABool( i1 <= i2 ))::s, g, o, d)
        (* Instead of using this implementation of tuple I could do it on this stack as well! Doint nothing to answers below, and if I don't have faulty opc *)
        |( s, g, TUP(oll)::o, d) -> execute((Atuple( List.map (executeCurry execute [] g []) oll ))::s, g, o, d)
        |((Atuple l)::s, g, PROJ(i)::o, d) -> execute( (List.nth l i)::s, g, o, d )
        |(s, g, CLOSURE(x, ol)::o, d) -> execute( (AClosure(g,x,ol)::s, g, o, d) )
        |(a::AClosure(g', x, ol)::s, g, APPLY::o, d) -> execute([], (x,a)::g, ol, (s, g, o)::d)
        (* Could have declared type state = State of a*b*c but why/why not to introduce constructor ? *)
        |(a::s', g'', RET::c'', (s, g, o)::d) -> execute(a::s, g, o, d)
        



        


