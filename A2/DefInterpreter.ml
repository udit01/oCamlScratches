(* 
Author -> Udit Jain
Entry Number -> 2016CS10327 
 *)
(*
In this assignment, you will define the abstract syntax (data type exp) and a definitional interpreter eval for a simple arithmetic and boolean calculation language.
The expressions in the language are of the following forms

    Integer constants, 
    Unary arithmetic operations: abs, (and any other sensible ones you can think of),
    Identifiers, represented as (alphanumeric) strings
    binary operations: + (addition), - (subtraction), * (Multiplication), div, mod, ^ (exponentiation)
    Boolean constants: T and F
    Unary boolean operation: not
    binary boolean operations:  /\ (and), \/ (or), -> (Impl)
    Comparison operators: = (equal) , > (greater than), < (less than) , >= (greater or equal), <= (less or equal) on integer expressions
    n-tuples for each n > 2
    Projection operators proj(i,n) which project the ith element of an n-tuple.


Assume all inputs are of proper type (we will study type-checking later).  Define a suitable data type answer.
eval: exp -> answer.
Next, define a suitable set of opcodes for a stack-and-table machine to evaluate this language and define a compiler for this language to sequences of these opcodes.
compile: exp -> opcode list
Third, define the stack machine execution functions, which takes a sequence of opcodes and executes them starting from a given stack and table.
execute: stack * table * opcode list -> answer
Provide enough examples  
*)

(* type expBool =  *)

type variable = B of bool | I of int | S of string

type exp = 
        true | false 
        | Var of variable (*variable is arbitary you could change this and gamma*)
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
        | Gt of exp*exp
        | Lt of exp*exp
        | Gte of exp*exp
        | Lte of exp*exp

        (* can add logical (bitwise) and or xor etc ? *)

(* How to define nth tuples ? *)
(* then the projection fuction ? *)
(* Also introduce Vars of variable ? *)

type ans = AnswerInt of int | AnswerBool of bool

(* let g1 =  *)

exception NotABool
exception NotAnInt
exception ExpNotMatched
(* first define only for expInt then generalize  *)
(* Eval function from exp -> Answer *)
let rec eval gamma  e = match e with
        true -> AnswerBool true
        | false -> AnswerBool false
        | Var v -> gamma v
        | Not e1 -> AnswerBool (not ( match (eval gamma e1) with
                                        AnswerBool b -> b
                                        | _ -> raise NotABool ) )
        | Or (e1, e2) -> AnswerBool((match (eval gamma e1) with
                                        AnswerBool b1 -> b1
                                        | _ -> raise NotABool
                                        )
                                        ||(match (eval gamma e2) with 
                                        AnswerBool b2 -> b2
                                        | _ -> raise NotABool
                                        ))
        | And (e1, e2) -> AnswerBool((match (eval gamma e1) with
                                        AnswerBool b1 -> b1
                                        | _ -> raise NotABool
                                        )
                                        &&(match (eval gamma e2) with 
                                        AnswerBool b2 -> b2
                                        | _ -> raise NotABool
                                        ))
        | Xor (e1, e2) -> AnswerBool(match 
                                                ((match (eval gamma e1) with
                                                AnswerBool b1 -> b1
                                                | _ -> raise NotABool
                                                ),
                                                (match (eval gamma e2) with 
                                                AnswerBool b2 -> b2
                                                | _ -> raise NotABool
                                                ))

                                                with 
                                                  (true,true)   -> false
                                                  | (true,false)  -> true
                                                  | (false,true)  -> true
                                                  | (false,false) -> false
                                                )
        | Impl (e1, e2) -> AnswerBool(match 
                                                ((match (eval gamma e1) with
                                                AnswerBool b1 -> b1
                                                | _ -> raise NotABool
                                                ),
                                                (match (eval gamma e2) with 
                                                AnswerBool b2 -> b2
                                                | _ -> raise NotABool
                                                ))

                                                with 
                                                  (true,true)   -> true
                                                  | (true,false)  -> false
                                                  | (false,true)  -> true
                                                  | (false,false) -> true
                                                )
        
        | Const n -> AnswerInt n
        | Mod e1 -> ( let a = eval gamma e1 in
                      let b = (match a with
                                AnswerInt i -> i
                                | _ -> raise NotAnInt )in
                        AnswerInt (if (b>=0) then b else (-1*b)) )
        | Add (e1,e2) -> AnswerInt ( (match (eval gamma e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        +
                                      (match (eval gamma e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )
        | Sub (e1,e2) -> AnswerInt ( (match (eval gamma e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        -
                                      (match (eval gamma e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )
        | Mul (e1,e2) -> AnswerInt ( (match (eval gamma e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        *
                                      (match (eval gamma e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )
        | Div (e1,e2) -> AnswerInt ( (match (eval gamma e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        /
                                      (match (eval gamma e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )
        | Pow (e1,e2) -> AnswerInt ( int_of_float(float_of_int(match (eval gamma e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt)
                                        **
                                      float_of_int(match (eval gamma e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt) ) )
        | Max (e1,e2) -> AnswerInt ( max (match (eval gamma e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        
                                      (match (eval gamma e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )
        | Min (e1,e2) -> AnswerInt ( min (match (eval gamma e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        
                                      (match (eval gamma e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )
        | Gt (e1,e2) -> AnswerBool ( (match (eval gamma e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        >
                                      (match (eval gamma e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )
        | Lt (e1,e2) -> AnswerBool ( (match (eval gamma e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        <
                                      (match (eval gamma e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )
        | Gte (e1,e2) -> AnswerBool ( (match (eval gamma e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        >=
                                      (match (eval gamma e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )
        | Lte (e1,e2) -> AnswerBool ( (match (eval gamma e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        <=
                                      (match (eval gamma e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )
        (* | _ -> raise ExpNotMatched *)


type opcode = TRUE 
            | FALSE 
            | LOOKUP of variable
            | NOT 
            | OR 
            | AND
            | XOR
            | IMPL
            | CONST of int
            | MOD
            | ADD
            | SUB
            | MUL
            | DIV
            | POW
            | MAX
            | MIN
            | GT
            | LT
            | GTE
            | LTE

exception OpcodeNotMatched

let rec compile e = match e with
        true ->  [TRUE]
        | false -> [FALSE]
        | Var v -> [LOOKUP(v)]
        | Not (e1) -> (compile e1) @ [NOT]
        | Or (e1, e2) -> (compile e1) @ (compile e2) @ [OR]
        | And (e1, e2) -> (compile e1) @ (compile e2) @ [AND]
        | Xor (e1, e2) -> (compile e1) @ (compile e2) @ [XOR]
        | Impl (e1, e2) ->  (compile e1) @ (compile e2) @ [IMPL]
        | Const (n) -> [CONST (n)]
        | Mod (e1) -> (compile e1) @ [MOD]
        | Add (e1,e2) -> (compile e1) @ (compile e2) @ [ADD]
        | Sub (e1,e2) -> (compile e1) @ (compile e2) @ [SUB]
        | Mul (e1,e2) -> (compile e1) @ (compile e2) @ [MUL]
        | Div (e1,e2) -> (compile e1) @ (compile e2) @ [DIV]
        | Pow (e1,e2) ->  (compile e1) @ (compile e2) @ [POW]
        | Max (e1,e2) ->  (compile e1) @ (compile e2) @ [MAX]
        | Min (e1,e2) ->  (compile e1) @ (compile e2) @ [MIN]
        | Gt (e1,e2) -> (compile e1) @ (compile e2) @ [GT]
        | Lt (e1,e2) -> (compile e1) @ (compile e2) @ [LT]
        | Gte (e1,e2) -> (compile e1) @ (compile e2) @ [GTE]
        | Lte (e1,e2) -> (compile e1) @ (compile e2) @ [LTE]
        (* | _ -> raise OpcodeNotMatched *)


(* execute: stack * table * opcode list -> answer *)
exception RuntimeError
let rec execute (stack, gamma, opcodes) = match (stack, gamma, opcodes) with
        (a::s , g, []) -> a
        |(s , g, TRUE::o ) -> execute ( (AnswerBool true )::(s) , g , o  )
        | (s , g, FALSE::o ) -> execute ( (AnswerBool false )::(s) , g , o  )
        | (s, g , LOOKUP(v)::o) -> execute ( ( g v  )::(s) , g , o  )
        | (a::s, g, NOT::o ) -> execute ( AnswerBool (not (match a with 
                                                AnswerBool b -> b
                                                | _ -> raise NotABool))::s , g, o  )
        | (a1::a2::s , g, OR::o ) -> execute (AnswerBool((match (a1) with
                                                AnswerBool b1 -> b1
                                                | _ -> raise NotABool
                                                )
                                                ||(match (a2) with 
                                                AnswerBool b2 -> b2
                                                | _ -> raise NotABool
                                                ))::s , g, o )
        | (a1::a2::s , g, AND::o ) -> execute (AnswerBool((match (a1) with
                                                AnswerBool b1 -> b1
                                                | _ -> raise NotABool
                                                )
                                                &&(match (a2) with 
                                                AnswerBool b2 -> b2
                                                | _ -> raise NotABool
                                                ))::s , g, o )
        | (a1::a2::s , g, XOR::o ) -> execute (AnswerBool(match 
                                                ((match (a1) with
                                                AnswerBool b1 -> b1
                                                | _ -> raise NotABool
                                                ),
                                                (match (a2) with 
                                                AnswerBool b2 -> b2
                                                | _ -> raise NotABool
                                                ))

                                                with 
                                                  (true,true)   -> false
                                                  | (true,false)  -> true
                                                  | (false,true)  -> true
                                                  | (false,false) -> false
                                                )::s, g , o)
        | (a1::a2::s , g, IMPL::o )  -> execute ( AnswerBool(match 
                                                ((match (a1) with
                                                AnswerBool b1 -> b1
                                                | _ -> raise NotABool
                                                ),
                                                (match (a2) with 
                                                AnswerBool b2 -> b2
                                                | _ -> raise NotABool
                                                ))
                                                with 
                                                  (true,true)   -> true
                                                  | (true,false)  -> false
                                                  | (false,true)  -> true
                                                  | (false,false) -> true
                                                )::s , g, o)
        
        | ( s, g, CONST(n)::o )-> execute( (AnswerInt n)::s, g, o)
        | ( a1::s, g, MOD::o ) -> (let b = (match (a1) with
                                                AnswerInt i -> i
                                                | _ -> raise NotAnInt )in
                                execute ( AnswerInt (if (b>=0) then b else (-1*b))::s , g, o ) )
        | (a1::a2::s, g, ADD::o) -> execute (AnswerInt ( (match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        +
                                      (match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt))::s, g, o )
        | (a1::a2::s, g, SUB::o) -> execute (AnswerInt ( (match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        -
                                      (match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt))::s, g, o)
        | (a1::a2::s, g, MUL::o) ->execute (AnswerInt ( (match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        *
                                      (match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt))::s, g, o )
        |  (a1::a2::s, g, DIV::o) ->execute (AnswerInt ( (match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        /
                                      (match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt))::s, g, o )
        | (a1::a2::s, g, POW::o)  ->execute ( AnswerInt ( int_of_float(float_of_int(match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt)
                                        **
                                      float_of_int(match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt) ))::s , g, o )
        | (a1::a2::s, g, MAX::o) -> execute ( AnswerInt ( max (match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        
                                      (match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )::s, g, o)
        | (a1::a2::s, g, MIN::o) -> execute ( AnswerInt ( min (match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        
                                      (match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )::s, g, o)
        | (a1::a2::s, g, GT::o) -> execute ( AnswerBool ( (match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        >
                                      (match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )::s, g, o )
        | (a1::a2::s, g, LT::o) -> execute( AnswerBool ( (match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        <
                                      (match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )::s, g, o)
        | (a1::a2::s, g, GTE::o)-> execute( AnswerBool ( (match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        >=
                                      (match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )::s, g, o)
        | (a1::a2::s, g, LTE::o)-> execute( AnswerBool ( (match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        <=
                                      (match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )::s, g, o)
        | _ -> raise RuntimeError
