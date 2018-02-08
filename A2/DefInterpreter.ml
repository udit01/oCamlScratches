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
    binary operations: + (addition), - (subtraction), * (multiplication), div, mod, ^ (exponentiation)
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
        | Implies of exp*exp
        | Const of int 
        | Mod of exp
        | Plus of exp*exp       
        | Subt of exp*exp       
        | Mult of exp*exp       
        | Div of exp*exp       
        | Pow of exp*exp
        | Max of exp*exp
        | Min of exp*exp
        | Gt of exp*exp
        | Lt of exp*exp
        | Gte of exp*exp
        | Lte of exp*exp

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
        | Not e1 -> let  ab1 = eval e1 in
                        let bans = (match ab1 with
                                AnswerBool b1 -> b1
                                | _ -> raise NotABool) in
                        AnswerBool (not bans)
        | Const n -> AnswerInt n
        | Mod e1 -> ( let a = eval e1 in
                      let b = (match a with
                                AnswerInt i -> i
                                | _ -> raise NotAnInt )in
                        AnswerInt (if (b>=0) then b else (-1*b)) )
        | Plus (e1,e2) -> (let a1 = eval e1 in
                          let a2 = eval e2 in 
                          let ans = (match a1 with 
                                AnswerInt i1 -> (match a2 with 
                                                        AnswerInt i2 -> (i1+i2)
                                                       | _ -> raise NotAnInt)
                                |_ -> raise NotAnInt) in
                           AnswerInt ans)

        | _ -> raise ExpNotMatched