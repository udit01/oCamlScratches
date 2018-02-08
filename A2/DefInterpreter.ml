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
    binary boolean operations:  /\ (and), \/ (or), -> (implies)
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

type exp = 
        true | false 
        | Not of exp
        | Or of exp*exp
        | And of exp*exp
        | Xor of exp*exp
        | Implies of exp*exp
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
(* Also introduce Vars of string ? *)

type ans = AnswerInt of int | AnswerBool of bool

exception NotABool
exception NotAnInt
exception ExpNotMatched
(* first define only for expInt then generalize  *)
(* Eval function from exp -> Answer *)
let rec eval e = match e with
        true -> AnswerBool true
        | false -> AnswerBool false
        | Not e1 -> AnswerBool (not ( match (eval e1) with
                                        AnswerBool b -> b
                                        | _ -> raise NotABool ) )
        | Or (e1, e2) -> AnswerBool((match (eval e1) with
                                        AnswerBool b1 -> b1
                                        | _ -> raise NotABool
                                        )
                                        ||(match (eval e2) with 
                                        AnswerBool b2 -> b2
                                        | _ -> raise NotABool
                                        ))
        | And (e1, e2) -> AnswerBool((match (eval e1) with
                                        AnswerBool b1 -> b1
                                        | _ -> raise NotABool
                                        )
                                        &&(match (eval e2) with 
                                        AnswerBool b2 -> b2
                                        | _ -> raise NotABool
                                        ))
        | Xor (e1, e2) -> AnswerBool(match 
                                                ((match (eval e1) with
                                                AnswerBool b1 -> b1
                                                | _ -> raise NotABool
                                                ),
                                                (match (eval e2) with 
                                                AnswerBool b2 -> b2
                                                | _ -> raise NotABool
                                                ))

                                                with 
                                                  (true,true)   -> false
                                                  | (true,false)  -> true
                                                  | (false,true)  -> true
                                                  | (false,false) -> false
                                                )
        | Implies (e1, e2) -> AnswerBool(match 
                                                ((match (eval e1) with
                                                AnswerBool b1 -> b1
                                                | _ -> raise NotABool
                                                ),
                                                (match (eval e2) with 
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
        | Mod e1 -> ( let a = eval e1 in
                      let b = (match a with
                                AnswerInt i -> i
                                | _ -> raise NotAnInt )in
                        AnswerInt (if (b>=0) then b else (-1*b)) )
        | Add (e1,e2) -> AnswerInt ( (match (eval e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        +
                                      (match (eval e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )
        | Sub (e1,e2) -> AnswerInt ( (match (eval e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        -
                                      (match (eval e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )
        | Mul (e1,e2) -> AnswerInt ( (match (eval e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        *
                                      (match (eval e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )
        | Div (e1,e2) -> AnswerInt ( (match (eval e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        /
                                      (match (eval e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )
        | Pow (e1,e2) -> AnswerInt ( int_of_float(float_of_int(match (eval e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt)
                                        **
                                      float_of_int(match (eval e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt) ) )
        | Max (e1,e2) -> AnswerInt ( max (match (eval e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        
                                      (match (eval e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )
        | Min (e1,e2) -> AnswerInt ( min (match (eval e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        
                                      (match (eval e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )
        | Gt (e1,e2) -> AnswerBool ( (match (eval e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        >
                                      (match (eval e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )
        | Lt (e1,e2) -> AnswerBool ( (match (eval e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        <
                                      (match (eval e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )
        | Gte (e1,e2) -> AnswerBool ( (match (eval e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        >=
                                      (match (eval e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )
        | Lte (e1,e2) -> AnswerBool ( (match (eval e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        <=
                                      (match (eval e2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )
        (* | _ -> raise ExpNotMatched *)


type opcode = TRUE 
            | FALSE 
            | NOT 
            | OR 
            | AND
            | XOR
            | IMPLIES
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

let rec compile e = match e with
        true ->  [TRUE]
        | false -> [FALSE]
        | Not e1 -> (compile e1) @ [NOT]
        | Or (e1, e2) -> (compile e1) @ (compile e2) @ [OR]
        | And (e1, e2) -> (compile e1) @ (compile e2) @ [AND]
        | Xor (e1, e2) -> (compile e1) @ (compile e2) @ [XOR]
        | Implies (e1, e2) ->  (compile e1) @ (compile e2) @ [IMPLIES]
        | Const n -> [CONST n]
        | Mod e1 -> (compile e1) @ [MOD]
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
