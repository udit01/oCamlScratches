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
            (* | V of variable variable is arbitary you could change this and gamma *)
            | Not of exp
            | Or of exp*exp
            | And of exp*exp
            | Xor of exp*exp
            | Impl of exp*exp
            (* | Const of int  *)
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
            (* | L of lambda *)
            (* | Apply of exp * exp *)
            | Ifte of exp * exp * exp
            (* If e1 then e2 else e3 ^^ *)
            | Let of variable * exp * exp 
            (* Let x = e1 in e2 ^^ *)
            | Def of ((variable*exp) list)\
            (* | A of answer *)
(* Answer of type value closure  *)

(* 
Closure is Table * Expression
Table is Variable -> Closure 
*)

(* type closure = Cl of table * exp
  and table = (variable, closure) Hashtbl.t ;;


type closure = Cl of table * exp
and table = variable -> closure ;; *)


type closure = Null |  Cl of table * exp | VClosure of table * answer 
and table = (variable * closure) list ;;

type answer = ABool of bool
              | AInt of int
              | Atup of int*answer

(* VClosure of table * exp  *)

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
        | ( Cl (gamma , true ) , [] ) -> VClosure(gamma, ABool true) 
        (* Change to A (ABool true) ^ if required *)
        | ( Cl (gamma , false) , [] ) -> VClosure(gamma, ABool false)
        | ( Cl (gamma , C i  ) , [] ) -> VClosure(gamma, AInt i)  
        
        (* 
        | ( Cl (gamma , A (ABool true) ) , [] ) -> VClosure(gamma,ABool true) 
        | ( Cl (gamma , A (ABool false)) , [] ) -> VClosure(gamma,ABool false)
        | ( Cl (gamma , A (AInt i)     ) , [] ) -> VClosure(gamma, AInt i)   *)


        (* | ( Cl (gamma , A a ) , [] ) -> VClosure(gamma, a) All In one case ?  *)

        | ( Cl (gamma , V v  ) , stack ) -> execute ( lookup gamma v , stack ) 
        | ( Cl (gamma', Lambda(v, exp')) , (Cl(gamma,exp))::stack ) -> execute ( Cl ( (v, Cl(gamma,exp))::gamma' ,  exp' ) , stack ) 
        (* | ( Cl (gamma', Lambda(v, exp')) , [] ) -> raise ExpectedClosureOnStack *)
        | ( Cl (gamma , Apply(exp1,exp2)) , stack) -> execute( Cl(gamma,exp1) , (Cl(gamma,exp2))::stack  ) 

        | ( Cl (gamma , Not(e)) , stack) -> execute( Cl(gamma,e) , ((NOT_)::stack  ) 
        | ( Cl (gamma , true ) , NOT_::stack) -> execute( Cl(gamma, false) , (stack) ) 
        | ( Cl (gamma , false ) , NOT_::stack) -> execute( Cl(gamma, true) , (stack) ) 

        | ( Cl (gamma , Or(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( OR_(e2)::stack  )         
        | ( Cl (gamma , true ) , OR_(e2)::stack) -> execute( Cl(gamma, true ) , ( stack ) )         
        | ( Cl (gamma , false ) , OR_(e2)::stack) -> execute( Cl(gamma, e2 ) , ( stack ) )

        | ( Cl (gamma , And(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( AND_(e2)::stack  )         
        | ( Cl (gamma , true ) , AND_(e2)::stack) -> execute( Cl(gamma, e2 ) , ( stack ) )         
        | ( Cl (gamma , false ), AND_(e2)::stack) -> execute( Cl(gamma, false ) , ( stack ) )   

        | ( Cl (gamma , Xor(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( XOR_(e2)::stack  )         
        | ( Cl (gamma , true ) , XOR_(e2)::stack) -> execute( Cl(gamma, e2 ) , ( XOR__(ABool true )::stack ) )         
        | ( Cl (gamma , false ), XOR_(e2)::stack) -> execute( Cl(gamma, e2 ) , ( XOR__(ABool false)::stack ) )
        | ( Cl (gamma , true ) , XOR__(ABool true )::stack) -> execute( Cl(gamma, false) , (stack) )         
        | ( Cl (gamma , true ) , XOR__(ABool false)::stack) -> execute( Cl(gamma, true ) , (stack) )         
        | ( Cl (gamma , false) , XOR__(ABool true )::stack) -> execute( Cl(gamma, true ) , (stack) )         
        | ( Cl (gamma , false) , XOR__(ABool false)::stack) -> execute( Cl(gamma, false) , (stack) )         

        | ( Cl (gamma , Impl(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( IMPL_(e2)::stack  )         
        | ( Cl (gamma , true ) , IMPL_(e2)::stack) -> execute( Cl(gamma, e2 ) , ( IMPL__(ABool true )::stack ) )         
        | ( Cl (gamma , false ), IMPL_(e2)::stack) -> execute( Cl(gamma, e2 ) , ( IMPL__(ABool false)::stack ) )
        | ( Cl (gamma , true ) , IMPL__(ABool true )::stack) -> execute( Cl(gamma, true ) , (stack) )         
        | ( Cl (gamma , true ) , IMPL__(ABool false)::stack) -> execute( Cl(gamma, true ) , (stack) )         
        | ( Cl (gamma , false) , IMPL__(ABool true )::stack) -> execute( Cl(gamma, false) , (stack) ) (*Because the one already on the stack was a1*)         
        | ( Cl (gamma , false) , IMPL__(ABool false)::stack) -> execute( Cl(gamma, true ) , (stack) )         

        | ( Cl (gamma , Mod(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( MOD_(e2)::stack  )         
        | ( Cl (gamma , C i1 ) , MOD_(e2)::stack) -> execute( Cl(gamma, e2 ) , ( MOD__(C i1)::stack ) )         
        | ( Cl (gamma , C i2 ) , MOD__(C i1)::stack) -> execute( Cl(gamma, C (i1 mod i2) ) , (stack ) )

        | ( Cl (gamma , Abs(e)) , stack) -> execute( Cl(gamma,e) , ((ABS_)::stack  ) 
        | ( Cl (gamma , C i ) , ABS_::stack) -> execute( Cl(gamma, C (abs i)) , (stack) ) 

        | ( Cl (gamma , Add(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( ADD_(e2)::stack  )         
        | ( Cl (gamma , C i1 ) , ADD_(e2)::stack) -> execute( Cl(gamma, e2 ) , ( ADD__(C i1)::stack ) )         
        | ( Cl (gamma , C i2 ) , ADD__(C i1)::stack) -> execute( Cl(gamma, C (i1 + i2) ) , (stack ) )

        | ( Cl (gamma , Sub(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( SUB_(e2)::stack  )         
        | ( Cl (gamma , C i1 ) , SUB_(e2)::stack) -> execute( Cl(gamma, e2 ) , ( SUB__(C i1)::stack ) )         
        | ( Cl (gamma , C i2 ) , SUB__(C i1)::stack) -> execute( Cl(gamma, C (i1 - i2) ) , (stack ) )

        | ( Cl (gamma , Mul(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( MUL_(e2)::stack  )         
        | ( Cl (gamma , C i1 ) , MUL_(e2)::stack) -> execute( Cl(gamma, e2 ) , ( MUL__(C i1)::stack ) )         
        | ( Cl (gamma , C i2 ) , MUL__(C i1)::stack) -> execute( Cl(gamma, C (i1 * i2) ) , (stack ) )

        | ( Cl (gamma , Div(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( DIV_(e2)::stack  )         
        | ( Cl (gamma , C i1 ) , DIV_(e2)::stack) -> execute( Cl(gamma, e2 ) , ( DIV__(C i1)::stack ) )         
        | ( Cl (gamma , C i2 ) , DIV__(C i1)::stack) -> execute( Cl(gamma, C (i1 / i2) ) , (stack ) )
 
        | ( Cl (gamma , Pow(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( POW_(e2)::stack  )         
        | ( Cl (gamma , C i1 ) , POW_(e2)::stack) -> execute( Cl(gamma, e2 ) , ( POW__(C i1)::stack ) )         
        | ( Cl (gamma , C i2 ) , POW__(C i1)::stack) -> execute( Cl(gamma, C (int_of_float(float_of_int(i1) ** float_of_int(i2))) ) , (stack ) )

        | ( Cl (gamma , MAX(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( MAX_(e2)::stack  )         
        | ( Cl (gamma , C i1 ) , MAX_(e2)::stack) -> execute( Cl(gamma, e2 ) , ( MAX__(C i1)::stack ) )         
        | ( Cl (gamma , C i2 ) , MAX__(C i1)::stack) -> execute( Cl(gamma, C (max i1 i2) ) , (stack ) )
        
        | ( Cl (gamma , MIN(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( MIN_(e2)::stack  )         
        | ( Cl (gamma , C i1 ) , MIN_(e2)::stack) -> execute( Cl(gamma, e2 ) , ( MIN__(C i1)::stack ) )         
        | ( Cl (gamma , C i2 ) , MIN__(C i1)::stack) -> execute( Cl(gamma, C (i1 / i2) ) , (stack ) )
        
        | ( Cl (gamma , EQL(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( EQL_(e2)::stack  )         
        | ( Cl (gamma , C i1 ) , EQL_(e2)::stack) -> execute( Cl(gamma, e2 ) , ( EQL__(C i1)::stack ) )         
        | ( Cl (gamma , C i2 ) , EQL__(C i1)::stack) -> execute( Cl(gamma, C (i1 / i2) ) , (stack ) )
        
        | ( Cl (gamma , GT(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( GT_(e2)::stack  )         
        | ( Cl (gamma , C i1 ) , GT_(e2)::stack) -> execute( Cl(gamma, e2 ) , ( GT__(C i1)::stack ) )         
        | ( Cl (gamma , C i2 ) , GT__(C i1)::stack) -> execute( Cl(gamma, C (i1 / i2) ) , (stack ) )
        
        | ( Cl (gamma , LT(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( LT_(e2)::stack  )         
        | ( Cl (gamma , C i1 ) , LT_(e2)::stack) -> execute( Cl(gamma, e2 ) , ( LT__(C i1)::stack ) )         
        | ( Cl (gamma , C i2 ) , LT__(C i1)::stack) -> execute( Cl(gamma, C (i1 / i2) ) , (stack ) )
        
        | ( Cl (gamma , GTE(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( GTE_(e2)::stack  )         
        | ( Cl (gamma , C i1 ) , GTE_(e2)::stack) -> execute( Cl(gamma, e2 ) , ( GTE__(C i1)::stack ) )         
        | ( Cl (gamma , C i2 ) , GTE__(C i1)::stack) -> execute( Cl(gamma, C (i1 / i2) ) , (stack ) )
        
        | ( Cl (gamma , LTE(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( LTE_(e2)::stack  )         
        | ( Cl (gamma , C i1 ) , LTE_(e2)::stack) -> execute( Cl(gamma, e2 ) , ( LTE__(C i1)::stack ) )         
        | ( Cl (gamma , C i2 ) , LTE__(C i1)::stack) -> execute( Cl(gamma, C (i1 / i2) ) , (stack ) )

        | ( Cl (gamma , Tuple (n, hd::tl) ) , stack) -> execute( Cl(gamma, hd ) , ( ProcTuple(n-1, tl,0 , [])::stack  )         
        | ( Cl (gamma , A a ) , ProcTuple( 0, [],  0, [])::stack) ->          
        | ( Cl (gamma , A a ) , ProcTuple( k, l ,  0, [])::stack) ->          
        | ( Cl (gamma , A a ) , ProcTuple( m, l1,  n, l2)::stack) ->          
        | ( Cl (gamma , A a ) , ProcTuple( 0, [],  k, l)::stack) ->          
        
        

        | _ -> raise MalformedExp

(* For Tuples or anything, make a tuple of closures, because the unit is not exp, it's closures *)