(* 
Author -> Udit Jain
Entry Number -> 2016CS10327 

PROBLEM STATEMENT 
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

(* EXAMPLES ARE PROVIDES AT THE END *)
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
        | EqI of exp*exp
        | Gt of exp*exp
        | Lt of exp*exp
        | Gte of exp*exp
        | Lte of exp*exp
        | Tuple of (exp list)
        | Proj of int * (exp)

type ans = AnswerInt of int | AnswerBool of bool | AnswerTuple of ans list

exception NotABool
exception NotAnInt
exception NotATuple
exception ExpNotMatched
(* Eval function from exp-> (table) -> Answer *)
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
        | EqI (e1,e2) -> AnswerBool ( (match (eval gamma e1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        =
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
        | Tuple l -> AnswerTuple (List.map (eval gamma) l)
        | Proj (i,Tuple l) -> eval gamma (List.nth  l i)
        | Proj (i, _) -> raise NotATuple
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
            | EQI
            | GT
            | LT
            | GTE
            | LTE
            | TUPLE
            | PROJ of int
            | TUP of ((opcode list) list)

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
        | EqI (e1,e2) -> (compile e1) @ (compile e2) @ [EQI]
        | Gt (e1,e2) -> (compile e1) @ (compile e2) @ [GT]
        | Lt (e1,e2) -> (compile e1) @ (compile e2) @ [LT]
        | Gte (e1,e2) -> (compile e1) @ (compile e2) @ [GTE]
        | Lte (e1,e2) -> (compile e1) @ (compile e2) @ [LTE]
        | Tuple l -> [TUP (List.map compile l)] @ [TUPLE]
        | Proj (i,Tuple l) -> [TUP(List.map compile l)] @ [PROJ(i)]
        | Proj (i,_) -> raise NotATuple
        (* | Proj (i,l) -> (compile(List.nth l i))  *)
        (* | _ -> raise OpcodeNotMatched *)
(* Two ways to do projection, either don't even compile others or you can reject it at execution *)

exception RuntimeError
let executeCurry execute stack gamma opcodelist = execute (stack,gamma,opcodelist)
(* NOTE: Remember that while pushing in stack, first operand goes inside
So the order of execution is reversed *)
(* execute: stack * table * opcode list -> answer *)
let rec execute (stack, gamma, opcodes) = match (stack, gamma, opcodes) with
        (a::s , g, []) -> a
        |(s , g, TRUE::o ) -> execute ( (AnswerBool true )::(s) , g , o  )
        | (s , g, FALSE::o ) -> execute ( (AnswerBool false )::(s) , g , o  )
        | (s, g , LOOKUP(v)::o) -> execute ( ( g v  )::(s) , g , o  )
        | (a::s, g, NOT::o ) -> execute ( AnswerBool (not (match a with 
                                                AnswerBool b -> b
                                                | _ -> raise NotABool))::s , g, o  )
        | (a2::a1::s , g, OR::o ) -> execute (AnswerBool((match (a1) with
                                                AnswerBool b1 -> b1
                                                | _ -> raise NotABool
                                                )
                                                ||(match (a2) with 
                                                AnswerBool b2 -> b2
                                                | _ -> raise NotABool
                                                ))::s , g, o )
        | (a2::a1::s , g, AND::o ) -> execute (AnswerBool((match (a1) with
                                                AnswerBool b1 -> b1
                                                | _ -> raise NotABool
                                                )
                                                &&(match (a2) with 
                                                AnswerBool b2 -> b2
                                                | _ -> raise NotABool
                                                ))::s , g, o )
        | (a2::a1::s , g, XOR::o ) -> execute (AnswerBool(match 
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
        | (a2::a1::s , g, IMPL::o )  -> execute ( AnswerBool(match 
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
        | (a2::a1::s, g, ADD::o) -> execute (AnswerInt ( (match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        +
                                      (match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt))::s, g, o )
        | (a2::a1::s, g, SUB::o) -> execute (AnswerInt ( (match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        -
                                      (match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt))::s, g, o)
        | (a2::a1::s, g, MUL::o) ->execute (AnswerInt ( (match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        *
                                      (match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt))::s, g, o )
        |  (a2::a1::s, g, DIV::o) ->execute (AnswerInt ( (match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        /
                                      (match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt))::s, g, o )
        | (a2::a1::s, g, POW::o)  ->execute ( AnswerInt ( int_of_float(float_of_int(match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt)
                                        **
                                      float_of_int(match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt) ))::s , g, o )
        | (a2::a1::s, g, MAX::o) -> execute ( AnswerInt ( max (match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        
                                      (match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )::s, g, o)
        | (a2::a1::s, g, MIN::o) -> execute ( AnswerInt ( min (match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        
                                      (match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )::s, g, o)
        | (a2::a1::s, g, EQI::o) -> execute ( AnswerBool ( (match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        =
                                      (match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )::s, g, o )
        | (a2::a1::s, g, GT::o) -> execute ( AnswerBool ( (match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        >
                                      (match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )::s, g, o )
        | (a2::a1::s, g, LT::o) -> execute( AnswerBool ( (match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        <
                                      (match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )::s, g, o)
        | (a2::a1::s, g, GTE::o)-> execute( AnswerBool ( (match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        >=
                                      (match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )::s, g, o)
        | (a2::a1::s, g, LTE::o)-> execute( AnswerBool ( (match (a1) with
                                        AnswerInt n1 -> n1
                                        | _ -> raise NotAnInt) 
                                        <=
                                      (match (a2) with
                                        AnswerInt n2 -> n2
                                        | _ -> raise NotAnInt)  )::s, g, o)
        | (s, g, TUP(oll)::TUPLE::o ) -> execute( (AnswerTuple ( List.map (executeCurry execute [] g) oll))::s ,g , o )
        | (s, g, TUP(oll)::PROJ(i)::o) -> execute ( [(execute( [] ,g , (List.nth oll i)))]@s , g, o)
        | _ -> raise RuntimeError


(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)
(* :::::::::::::::::::::::::::TESTS::::::::::::::::::::::::::: *)
(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)
let gamma v = match v with
        S str -> (match str with 
                        "x" -> AnswerInt(10)
                        |"y" -> AnswerInt(5)
                        | "true" -> AnswerBool(true)
                        | "false" -> AnswerBool(false)
                        | "random" -> AnswerBool(true)
                        |_ -> AnswerInt(2) )
        | _ -> AnswerInt(1)                
        

let e1 = (Gt( Mod(Const(-3) ) , Const(2) ))
let g1 = AnswerBool(true)

let e2 = (Lt( Mod(Const(-3) ) , Const(3) ))
let g2 = AnswerBool(false)

let e3 = Tuple ([e1;e2])
let g3 = AnswerTuple ([g1;g2])

let e4 = Proj(1, e3 )
let g4 = g2 

let e5 = Var ( S "x" )
let g5 = AnswerInt(10)
let e6 = Var ( S "y" )
let g6 = AnswerInt(5)

let e7 = Pow (e5,e6)
let g7 = AnswerInt(100000)

let e8 = EqI(Sub(Add(Const(2),Const(33)), Const(35)),Const(0))
let g8 = AnswerBool(true)

let e9 = Div( Mul(Pow(Const(5), Const(3)), Const(4)), Const(125) )
let g9 = AnswerInt(4)

let e10 = Impl(Gt(Add(Var (S "x"), Const(100)), Const(50)), Var( S "true"))
let g10 = AnswerBool(true)

let e11 = Not(Or(e8, Var (S "random")))
let g11 = AnswerBool(false)

let e12 = Gt(Mod(Const(-34)), Const(0))
let g12 = AnswerBool(true)

let e13 = Tuple ([e8; e9; e10; e11; e12]) (* == [true, 4, true, false, true] *)
let g13 = AnswerTuple([g8;g9;g10;g11;g12])

let e14 = Proj (3, e13) (* == exp3 false *)
let g14 = g11

let e15 = Not ( And (e14, false))
let g15 = AnswerBool(true)

let l = [e1;e2;e3;e4;e5;e6;e7;e8
        ;e9;e10;e11;e12;e13;e14;e15
        ];;
let gt = [g1;g2;g3;g4;g5;g6;g7;g8
        ;g9;g10;g11;g12;g13;g14;g15
        ];;

let rec checker i (l , gtr) = match (l,gtr) with
        ([],[]) -> (Printf.printf "Checking done for %d values.\n" i ) 
        | (x::xs,y::ys) -> ((if((execute ([],gamma,(compile x))) <> y ) then (Printf.printf "Execute(compile) =/= ground Truth for: %d\n " i) 
                        else if ((eval gamma x) <> y ) then (Printf.printf "Eval =/= ground Truth for %d\n " i)
                        else (Printf.printf "Success for: %d\n" i ) ) ; checker (i+1) (xs,ys) )
        | _ ->    (Printf.printf "Error in positioning of lables and input data : %d\n" i )  ;;          
checker 0 (l,gt);;