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
            | Ifte of exp * exp * exp
            (* If e1 then e2 else e3 ^^ *)
            | Let of variable * exp * exp 
            (* Let x = e1 in e2 ^^ *)
            | Def of ((variable*exp) list)
            (* 
            Def d1 in d2
            Sequential, Parallel definitions 
            Local scoping rules?  *)
and lambda = Lambda of variable * exp

(* Answer of type value closure  *)
(* No diffrence between Closure and ValueClosure for SECD machine? *)

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
            | TUP of (int)
            | PROJ of int
            | CLOSURE of variable * (opcode list)
            | RET
            | APPLY
            | IF 
            | THELSE of (opcode list) * (opcode list)
            | BIND of variable
            | UNBIND of variable
            | DEF of int 
            | MAP of variable * (opcode list)
            | BINDRET

type ans = N
          | AInt of int 
          | ABool of bool 
          | Atuple of (ans list) 
          | VCLosure of table * variable * (opcode list)
  and table = (variable * ans) list;;

type state = (ans list) * (table) * (opcode list)


(* type opcode =  *)
exception NotATuple
let mapCurry map compile (var, exp) = map(var, compile exp)

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
        | Eql (e1,e2) -> (compile e1) @ (compile e2) @ [EQL]
        | Gt (e1,e2) -> (compile e1) @ (compile e2) @ [GT]
        | Lt (e1,e2) -> (compile e1) @ (compile e2) @ [LT]
        | Gte (e1,e2) -> (compile e1) @ (compile e2) @ [GTE]
        | Lte (e1,e2) -> (compile e1) @ (compile e2) @ [LTE]
        | Tuple l -> (List.concat (List.map compile l)) @ [ TUP (List.length l)] 
        | Proj (i,e) -> (compile e) @[PROJ(i)]
        (* Could also have compiled only i'th of the tuple *)
        (* | Proj(i, Tuple l) -> compile (List.nth l i) *)
        (* | Proj (i,_) -> raise NotATuple *)
        | L ( Lambda (v, e) ) -> [CLOSURE(v,compile(e)@[RET])]
        | Apply (e1, e2) -> compile(e1) @ compile(e2) @ [APPLY]
        | Ifte(e1, e2, e3) -> [IF] @ (compile e1) @ [THELSE(compile e2, compile e3)]
        | Let (x, e1, e2) -> compile(e1) @ [BIND(x)] @ compile(e2) @[UNBIND(x)]
        (* | Def(l) -> [DEF(List.length l)] @ (List.map (mapCurry MAP compile) l) *)
        | Def(l) -> [DEF(List.length l)] @ ( let rec mapper l1 l2 = match l2 with 
                                                [] -> l1
                                             | (v, e)::tl -> mapper (MAP(v, compile e)::l1) (tl) 
                                              in  
                                              mapper [] l)
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
let rec lookup (t:table) (v:variable) : ans = match t with
      [] -> N
      | (v2, a)::tl -> if(v2 = v) then (a) else (lookup tl v)
      ;;

exception NotEnoughElems
let rec takeOutFirstN l n = 
      let rec tofn l n fl = match l with
      [] -> if (n = 0) then (fl) else (raise NotEnoughElems)
      | hd::tl -> if(n = 0) then (fl) else (tofn tl (n-1) (fl@[hd]))
      in 
      List.rev (tofn l n [])
      ;;

let rec afterN l n = match l with
      [] -> if (n = 0) then ([]) else (raise NotEnoughElems)
      | hd::tl -> if(n = 0) then (hd::tl) else (afterN tl (n-1))

let rec remFirstOcc (g:table) (x:variable) = 
    let rec rfo g x l =  match g with 
      [] -> l
      | (y, a)::tl -> if (y = x) then ( l@tl ) else (rfo tl x (l@[(y, a)]))
       in
      rfo g x [] 
      ;;
(* When a tuple forms do we have to evaluate all projections even if only 1 of them is required ? *)
exception RuntimeError
exception TypeMismatch
let executeCurry execute stack gamma dump opcodelist = execute (stack,gamma,opcodelist,dump)
(* Output of SECD is answer or full state ? *)
let rec execute ((stack: ans list), (gamma:table) , (opcodes:opcode list), dump) = 
        match (stack, gamma, opcodes, dump) with
        (a::s, g, [], d) -> a
        |(s, g, TRUE::o, d) -> execute ((ABool true)::s, g, o, d) 
        |(s, g, FALSE::o, d) -> execute ((ABool false)::s, g, o, d)
        |(s, g, LOOKUP(v)::o, d) -> execute((lookup g v)::s, g, o, d)
        (* |(s, g1@(v,a)@g2 , LOOKUP(v)::o, d) -> execute((a)::s, g, o, d) *)
        (* Is the above pattern matching allowed ? and if we have multiple then will it do it correctly ? ie pick the first one ? *)
        |((ABool b)::s, g, NOT::o, d) -> execute((ABool (not b))::s, g, o, d)
        |((ABool b2)::(ABool b1)::s, g, OR::o, d) -> execute((ABool (b1 || b2))::s, g, o, d)
        |((ABool b2)::(ABool b1)::s, g, AND::o, d) -> execute((ABool (b1 && b2))::s, g, o, d)
        |((ABool b2)::(ABool b1)::s, g, XOR::o, d) -> execute((ABool (
                                                      match (b1, b2) with 
                                                          (true,true)   -> false
                                                          |(true,false)  -> true
                                                          |(false,true)  -> true
                                                          |(false,false) -> false
                                                        ))::s, g, o, d)
        |((ABool b2)::(ABool b1)::s, g, IMPL::o, d) -> execute((ABool (
                                                      match (b1, b2) with 
                                                          (true,true)   -> true
                                                          |(true,false)  -> false
                                                          |(false,true)  -> true
                                                          |(false,false) -> true
                                                        ))::s, g, o, d)                                                        
        |(s, g, (CONST n)::o, d) -> execute((AInt n)::s, g, o, d)
        |((AInt i)::s, g, ABS::o, d) -> execute((AInt (abs i))::s, g, o, d)
        |((AInt i2)::(AInt i1)::s, g, MOD::o, d) -> execute((AInt( i1 mod i2 ))::s , g, o, d)
        |((AInt i2)::(AInt i1)::s, g, ADD::o, d) -> execute((AInt(i1 + i2))::s, g, o, d)
        |((AInt i2)::(AInt i1)::s, g, SUB::o, d) -> execute((AInt(i1 - i2))::s, g, o, d)
        |((AInt i2)::(AInt i1)::s, g, MUL::o, d) -> execute((AInt(i1 * i2))::s, g, o, d)
        |((AInt i2)::(AInt i1)::s, g, DIV::o, d) -> execute((AInt(i1 / i2))::s, g, o, d)
        |((AInt i2)::(AInt i1)::s, g, POW::o, d) -> execute((AInt( int_of_float( float_of_int(i1)**float_of_int(i2))))::s, g, o, d)
        |((AInt i2)::(AInt i1)::s, g, MAX::o, d) -> execute((AInt( max i1 i2 ))::s, g, o, d)
        |((AInt i2)::(AInt i1)::s, g, MIN::o, d) -> execute((AInt( min i1 i2 ))::s, g, o, d)
        |((AInt i2)::(AInt i1)::s, g, EQL::o, d) -> execute((ABool( i1 = i2 ))::s, g, o, d)
        |((AInt i2)::(AInt i1)::s, g, GT::o, d) -> execute((ABool( i1 > i2 ))::s, g, o, d)
        |((AInt i2)::(AInt i1)::s, g, LT::o, d) -> execute((ABool( i1 < i2 ))::s, g, o, d)
        |((AInt i2)::(AInt i1)::s, g, GTE::o, d) -> execute((ABool( i1 >= i2 ))::s, g, o, d)
        |((AInt i2)::(AInt i1)::s, g, LTE::o, d) -> execute((ABool( i1 <= i2 ))::s, g, o, d)
        (* Instead of using this implementation of tuple I could do it on this stack as well! Doint nothing to answers below, and if I don't have faulty opc *)
        |( s, g, TUP(k)::o, d) -> execute((Atuple( takeOutFirstN s k ))::(afterN s k), g, o, d)
        |((Atuple l)::s, g, PROJ(i)::o, d) -> execute( (List.nth l i)::s, g, o, d )
        |(s, g, CLOSURE(x, ol)::o, d) -> execute( (VCLosure(g,x,ol)::s, g, o, d) )
        |(a::VCLosure(g', x, ol)::s, g, APPLY::o, d) -> execute([], (x,a)::g, ol, (s, g, o)::d)
        (* Could have declared type state = State of a*b*c but why/why not to introduce constructor ? *)
        |(a::s', g'', RET::c'', (s, g, o)::d) -> execute(a::s, g, o, d)
        |(s, g, IF::o, d) -> execute(s, g, o, d)
        |((ABool true)::s, g, THELSE(ol1,ol2)::o, d) -> execute(s, g, ol1@o, d)
        |((ABool false)::s, g, THELSE(ol1,ol2)::o, d) -> execute(s, g, ol2@o, d)
        |(a::s, g, BIND(x)::o, d ) -> execute(s, (x,a)::g, o, d)
        |(s, g, UNBIND(x)::o, d )-> execute(s, remFirstOcc g x, o, d)
        |(s, g, DEF(1)::MAP(v,ol)::o, d) -> execute([],[],ol@[BINDRET],(s, g, BIND(v)::o)::d)
        |(s, g, DEF(n)::MAP(v,ol)::o, d) -> execute([],[],ol@[BINDRET],(s, g, BIND(v)::DEF(n-1)::o)::d)
        |(a::s', g', BINDRET::o', (s, g, BIND(v)::DEF(n)::o)::d ) -> execute (s, (v,a)::g, DEF(n)::o, d)
        | _ -> raise TypeMismatch
        ;;

(* TEST CASES::::::::::: *)


let v1 = Var "a" ;;
let x = Var "x" ;;
let y = Var "y" ;;

 let e1 = Apply( L (Lambda(x , Add(V (x),Const(3)))) , Const(7) ) ;;
execute( [], [], (compile e1) , [] );;
 let e2 = Ifte(true, e1, Const(5));;
execute( [], [], (compile e2) , [] );;
 let e3 = Let( Var "y" , e2, Mul(V (Var "y"),Const(2) ) );;
execute( [], [], (compile e3) , [] );;


let g = [(x,AInt 1); (y, AInt 2) ; (v1, ABool true)];;

let z = Var "z" ;;
let function1 = Lambda ( z , Add( Pow(V z, Const(2)) , Abs(V z) )  ) ;;
let function2 = Lambda ( z , Div( Proj(0, Tuple([V z;Const(2)]) ) , Const(3) ));;

let e4 = V y ;;
execute( [], g, (compile e4) , [] );;
let e5 = Apply( L function1, Const(-3) ) ;;
execute( [], g, (compile e5) , [] );;
let e6 = Tuple ([e1; e2; e3; e4; e5]) ;;
execute( [], g, (compile e6) , [] );;

let e7 = Not( And (V v1, true) ) ;; (*False*)
execute( [], g, (compile e7) , [] );;

let e8 = Xor(e7, Not e7) ;; (*True*)
execute( [], g, (compile e8) , [] );;

let e9 = Impl(e8, e7) ;; (*False*)
execute( [], g, (compile e9) , [] );;

let e10 = Apply ( L function2 , Const(55)) ;;
execute( [], g, (compile e10) , [] );;

