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


type answer = ABool of bool
              | AInt of int
              | Atup of int * (answer list)
(* VClosure of table * exp  *)


type exp =  NExp
            (* |true | false *)
            | B of bool
            | C of int (*Const of int*)
            | V of variable (*variable is arbitary you could change this and gamma*)
            | Lambda of variable * exp
            | Apply of exp * exp
            (* | V of variable variable is arbitary you could change this and gamma *)
            | NOT of exp| NOT_
            | OR of exp*exp  | OR_ of exp
            | AND of exp*exp | AND_ of exp 
            | XOR of exp*exp | XOR_ of exp | XOR__ of answer
            | IMPL of exp*exp | IMPL_ of exp | IMPL__ of answer
            | MOD of exp*exp | MOD_ of exp | MOD__ of answer
            | ABS of exp | ABS_ 
            | ADD of exp*exp | ADD_ of exp | ADD__ of answer       
            | SUB of exp*exp | SUB_ of exp | SUB__ of answer       
            | MUL of exp*exp | MUL_ of exp | MUL__ of answer       
            | DIV of exp*exp | DIV_ of exp | DIV__ of answer       
            | POW of exp*exp | POW_ of exp | POW__ of answer
            | MAX of exp*exp | MAX_ of exp | MAX__ of answer
            | MIN of exp*exp | MIN_ of exp | MIN__ of answer
            | EQL of exp*exp | EQL_ of exp | EQL__ of answer
            | GT of exp*exp | GT_ of exp | GT__ of answer
            | LT of exp*exp | LT_ of exp | LT__ of answer
            | GTE of exp*exp | GTE_ of exp | GTE__ of answer
            | LTE of exp*exp | LTE_ of exp | LTE__ of answer
            | Tuple of int*(exp list) | TUPLE_ of int*(answer list) | PROCTUPLE of int * (exp list) * int * (answer list)
            | Proj of int * (exp)
            (* | L of lambda *)
            (* | Apply of exp * exp *)
            | Ifte of exp * exp * exp | IFTE_ of exp * exp
            (* If e1 then e2 else e3 ^^ *)
            | Let of variable * exp * exp | LET_ of variable * exp
            (* Let x = e1 in e2 ^^ *)
            | Def of ((variable * closure) list)
            (* | A of answer *)
(* Answer of type value closure  *)

(* 
Closure is Table * Expression
Table is Variable -> Closure 
*)

(* type closure = Cl of table * exp
  AND table = (variable, closure) Hashtbl.t ;;


type closure = Cl of table * exp
AND table = variable -> closure ;; *)


and closure = Null |  Cl of table * exp | VClosure of table * answer | OPCl of exp
and table = (variable * closure) list ;;

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
        | ( Cl (gamma , B true ) , [] ) -> VClosure(gamma, ABool true) 
        (* Change to A (ABool true) ^ if required *)
        | ( Cl (gamma , B false) , [] ) -> VClosure(gamma, ABool false)
        | ( Cl (gamma , C i  ) , [] ) -> VClosure(gamma, AInt i)  
        | ( Cl (gamma , TUPLE_(i,al)), [] ) -> VClosure(gamma, Atup(i,al))
        
        (* 
        | ( Cl (gamma , A (ABool true) ) , [] ) -> VClosure(gamma,ABool true) 
        | ( Cl (gamma , A (ABool false)) , [] ) -> VClosure(gamma,ABool false)
        | ( Cl (gamma , A (AInt i)     ) , [] ) -> VClosure(gamma, AInt i)   *)


        (* | ( Cl (gamma , A a ) , [] ) -> VClosure(gamma, a) All In one case ?  *)

        | ( Cl (gamma , V v  ) , stack ) -> execute ( lookup gamma v , stack ) 
        | ( Cl (gamma', Lambda(v, exp')) , (Cl(gamma,exp))::stack ) -> execute ( Cl ( (v, Cl(gamma,exp))::gamma' ,  exp' ) , stack ) 
        (* | ( Cl (gamma', Lambda(v, exp')) , [] ) -> raise ExpectedClosureOnStack *)
        | ( Cl (gamma , Apply(exp1,exp2)) , stack) -> execute( Cl(gamma,exp1) , (Cl(gamma,exp2))::stack  ) 

        | ( Cl (gamma , NOT(e)) , stack) -> execute( Cl(gamma,e) , ((OPCl(NOT_))::stack  )) 
        | ( Cl (gamma , B true ) , OPCl(NOT_)::stack) -> execute( Cl(gamma, B false) , (stack) ) 
        | ( Cl (gamma , B false ) , OPCl(NOT_)::stack) -> execute( Cl(gamma, B true) , (stack) ) 

        | ( Cl (gamma , OR(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( OPCl(OR_(e2))::stack  ))         
        | ( Cl (gamma , B true ) , OPCl(OR_(e2))::stack) -> execute( Cl(gamma, B true ) , ( stack ) )         
        | ( Cl (gamma , B false ) , OPCl(OR_(e2))::stack) -> execute( Cl(gamma, e2 ) , ( stack ) )

        | ( Cl (gamma , AND(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( OPCl(AND_(e2))::stack  ))         
        | ( Cl (gamma , B true ) , OPCl(AND_(e2))::stack) -> execute( Cl(gamma, e2 ) , ( stack ) )         
        | ( Cl (gamma , B false ), OPCl(AND_(e2))::stack) -> execute( Cl(gamma, B false ) , ( stack ) )   

        | ( Cl (gamma , XOR(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( OPCl(XOR_(e2))::stack  ))         
        | ( Cl (gamma , B true ) , OPCl(XOR_(e2))::stack) -> execute( Cl(gamma, e2 ) , ( OPCl(XOR__(ABool true ))::stack ) )         
        | ( Cl (gamma , B false ), OPCl(XOR_(e2))::stack) -> execute( Cl(gamma, e2 ) , ( OPCl(XOR__(ABool false))::stack ) )
        | ( Cl (gamma , B true ) , OPCl(XOR__(ABool true ))::stack) -> execute( Cl(gamma, B false) , (stack) )         
        | ( Cl (gamma , B true ) , OPCl(XOR__(ABool false))::stack) -> execute( Cl(gamma, B true ) , (stack) )         
        | ( Cl (gamma , B false) , OPCl(XOR__(ABool true ))::stack) -> execute( Cl(gamma, B true ) , (stack) )         
        | ( Cl (gamma , B false) , OPCl(XOR__(ABool false))::stack) -> execute( Cl(gamma, B false) , (stack) )         

        | ( Cl (gamma , IMPL(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( OPCl(IMPL_(e2))::stack  ))         
        | ( Cl (gamma , B true ) , OPCl(IMPL_(e2))::stack) -> execute( Cl(gamma, e2 ) , ( OPCl(IMPL__(ABool true ))::stack ) )         
        | ( Cl (gamma , B false ), OPCl(IMPL_(e2))::stack) -> execute( Cl(gamma, e2 ) , ( OPCl(IMPL__(ABool false))::stack ) )
        | ( Cl (gamma , B true ) , OPCl(IMPL__(ABool true ))::stack) -> execute( Cl(gamma, B true ) , (stack) )         
        | ( Cl (gamma , B true ) , OPCl(IMPL__(ABool false))::stack) -> execute( Cl(gamma, B true ) , (stack) )         
        | ( Cl (gamma , B false) , OPCl(IMPL__(ABool true ))::stack) -> execute( Cl(gamma, B false) , (stack) ) (*Because the one already on the stack was a1*)         
        | ( Cl (gamma , B false) , OPCl(IMPL__(ABool false))::stack) -> execute( Cl(gamma, B true ) , (stack) )         

        | ( Cl (gamma , MOD(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( OPCl(MOD_(e2))::stack  ))         
        | ( Cl (gamma , C i1 ) , OPCl(MOD_(e2))::stack) -> execute( Cl(gamma, e2 ) , ( OPCl(MOD__(AInt i1))::stack ) )         
        | ( Cl (gamma , C i2 ) , OPCl(MOD__(AInt i1))::stack) -> execute( Cl(gamma, C (i1 mod i2) ) , (stack ) )

        | ( Cl (gamma , ABS(e)) , stack) -> execute( Cl(gamma,e) , ((OPCl(ABS_))::stack  )) 
        | ( Cl (gamma , C i ) , OPCl(ABS_)::stack) -> execute( Cl(gamma, C (abs i)) , (stack) ) 

        | ( Cl (gamma , ADD(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( OPCl(ADD_(e2))::stack  ))         
        | ( Cl (gamma , C i1 ) , OPCl(ADD_(e2))::stack) -> execute( Cl(gamma, e2 ) , ( OPCl(ADD__(AInt i1))::stack ) )         
        | ( Cl (gamma , C i2 ) , OPCl(ADD__(AInt i1))::stack) -> execute( Cl(gamma, C (i1 + i2) ) , (stack ) )

        | ( Cl (gamma , SUB(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( OPCl(SUB_(e2))::stack  ))         
        | ( Cl (gamma , C i1 ) , OPCl(SUB_(e2))::stack) -> execute( Cl(gamma, e2 ) , ( OPCl(SUB__(AInt i1))::stack ) )         
        | ( Cl (gamma , C i2 ) , OPCl(SUB__(AInt i1))::stack) -> execute( Cl(gamma, C (i1 - i2) ) , (stack ) )

        | ( Cl (gamma , MUL(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( OPCl(MUL_(e2))::stack  ))         
        | ( Cl (gamma , C i1 ) , OPCl(MUL_(e2))::stack) -> execute( Cl(gamma, e2 ) , ( OPCl(MUL__(AInt i1))::stack ) )         
        | ( Cl (gamma , C i2 ) , OPCl(MUL__(AInt i1))::stack) -> execute( Cl(gamma, C (i1 * i2) ) , (stack ) )

        | ( Cl (gamma , DIV(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( OPCl(DIV_(e2))::stack  ))         
        | ( Cl (gamma , C i1 ) , OPCl(DIV_(e2))::stack) -> execute( Cl(gamma, e2 ) , ( OPCl(DIV__(AInt i1))::stack ) )         
        | ( Cl (gamma , C i2 ) , OPCl(DIV__(AInt i1))::stack) -> execute( Cl(gamma, C (i1 / i2) ) , (stack ) )
 
        | ( Cl (gamma , POW(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( OPCl(POW_(e2))::stack  ))         
        | ( Cl (gamma , C i1 ) , OPCl(POW_(e2))::stack) -> execute( Cl(gamma, e2 ) , ( OPCl(POW__(AInt i1))::stack ) )         
        | ( Cl (gamma , C i2 ) , OPCl(POW__(AInt i1))::stack) -> execute( Cl(gamma, C (int_of_float(float_of_int(i1) ** float_of_int(i2))) ) , (stack ) )

        | ( Cl (gamma , MAX(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( OPCl(MAX_(e2))::stack  ))         
        | ( Cl (gamma , C i1 ) , OPCl(MAX_(e2))::stack) -> execute( Cl(gamma, e2 ) , ( OPCl(MAX__(AInt i1))::stack ) )         
        | ( Cl (gamma , C i2 ) , OPCl(MAX__(AInt i1))::stack) -> execute( Cl(gamma, C (max i1 i2) ) , (stack ) )
        
        | ( Cl (gamma , MIN(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( OPCl(MIN_(e2))::stack  ))         
        | ( Cl (gamma , C i1 ) , OPCl(MIN_(e2))::stack) -> execute( Cl(gamma, e2 ) , ( OPCl(MIN__(AInt i1))::stack ) )         
        | ( Cl (gamma , C i2 ) , OPCl(MIN__(AInt i1))::stack) -> execute( Cl(gamma, C (min i1 i2) ) , (stack ) )
        
        | ( Cl (gamma , EQL(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( OPCl(EQL_(e2))::stack  ))         
        | ( Cl (gamma , C i1 ) , OPCl(EQL_(e2))::stack) -> execute( Cl(gamma, e2 ) , ( OPCl(EQL__(AInt i1))::stack ) )         
        | ( Cl (gamma , C i2 ) , OPCl(EQL__(AInt i1))::stack) -> execute( Cl(gamma, B (i1 = i2) ) , (stack ) )
        
        | ( Cl (gamma , GT(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( OPCl(GT_(e2))::stack  ))         
        | ( Cl (gamma , C i1 ) , OPCl(GT_(e2))::stack) -> execute( Cl(gamma, e2 ) , ( OPCl(GT__(AInt i1))::stack ) )         
        | ( Cl (gamma , C i2 ) , OPCl(GT__(AInt i1))::stack) -> execute( Cl(gamma, B (i1 > i2) ) , (stack ) )
        
        | ( Cl (gamma , LT(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( OPCl(LT_(e2))::stack  ))         
        | ( Cl (gamma , C i1 ) , OPCl(LT_(e2))::stack) -> execute( Cl(gamma, e2 ) , ( OPCl(LT__(AInt i1))::stack ) )         
        | ( Cl (gamma , C i2 ) , OPCl(LT__(AInt i1))::stack) -> execute( Cl(gamma, B (i1 < i2) ) , (stack ) )
        
        | ( Cl (gamma , GTE(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( OPCl(GTE_(e2))::stack  ))         
        | ( Cl (gamma , C i1 ) , OPCl(GTE_(e2))::stack) -> execute( Cl(gamma, e2 ) , ( OPCl(GTE__(AInt i1))::stack ) )         
        | ( Cl (gamma , C i2 ) , OPCl(GTE__(AInt i1))::stack) -> execute( Cl(gamma, B (i1 >= i2) ) , (stack ) )
        
        | ( Cl (gamma , LTE(e1,e2)) , stack) -> execute( Cl(gamma,e1) , ( OPCl(LTE_(e2))::stack  ))         
        | ( Cl (gamma , C i1 ) , OPCl(LTE_(e2))::stack) -> execute( Cl(gamma, e2 ) , ( OPCl(LTE__(AInt i1))::stack ) )         
        | ( Cl (gamma , C i2 ) , OPCl(LTE__(AInt i1))::stack) -> execute( Cl(gamma, B (i1 <= i2) ) , (stack ) )

        | ( Cl (gamma, Ifte(e1, e2, e3)) , stack ) -> execute( Cl (gamma, e1) , OPCl(IFTE_(e2, e3))::stack )
        | ( Cl (gamma, B true ) , OPCl(IFTE_(e2, e3))::stack ) -> execute( Cl(gamma, e2) , stack )
        | ( Cl (gamma, B false) , OPCl(IFTE_(e2, e3))::stack ) -> execute( Cl(gamma, e3) , stack )

        | ( Cl (gamma, Let(v, e1, e2)) , stack ) -> execute( Cl (gamma, e1) , OPCl(LET_(v, e2))::stack )
        | ( Cl (gamma, a ) , OPCl(LET_(v, e2))::stack ) -> execute( Cl ((v, Cl(gamma,a))::gamma, e2) , stack )

        | ( Cl (gamma, Proj(i, Tuple(n, l)) ) , stack ) -> execute( Cl(gamma, List.nth l i) , stack )
       
        | ( Cl (gamma , Tuple (n, hd::tl) ) , stack) -> execute( Cl(gamma, hd ) , ( OPCl(PROCTUPLE(n-1, tl, 0, []))::stack  ))         
        | ( Cl (gamma , B b ) , OPCl(PROCTUPLE( 0, []    ,  0, []))::stack) -> execute( Cl(gamma, TUPLE_(1, [ABool b])) , stack )         
        | ( Cl (gamma , C i ) , OPCl(PROCTUPLE( 0, []    ,  0, []))::stack) -> execute( Cl(gamma, TUPLE_(1, [AInt i])) , stack )         
        | ( Cl (gamma , B b ) , OPCl(PROCTUPLE( 0, []    ,  k, l ))::stack) -> execute( Cl(gamma, TUPLE_(k+1, (ABool b)::l)) , stack)        
        | ( Cl (gamma , C i ) , OPCl(PROCTUPLE( 0, []    ,  k, l ))::stack) -> execute( Cl(gamma, TUPLE_(k+1, (AInt i)::l)) , stack)        
        | ( Cl (gamma , B b ) , OPCl(PROCTUPLE( k, h::t  ,  0, []))::stack) -> execute( Cl(gamma, h) , OPCl(PROCTUPLE( k-1, h::t,  1, [ABool b] ))::stack)         
        | ( Cl (gamma , C i ) , OPCl(PROCTUPLE( k, h::t  ,  0, []))::stack) -> execute( Cl(gamma, h) , OPCl(PROCTUPLE( k-1, h::t,  1, [AInt i] ))::stack)         
        | ( Cl (gamma , B b ) , OPCl(PROCTUPLE( m, h1::t1,  n, l2))::stack) -> execute( Cl(gamma, h1), OPCl(PROCTUPLE( m-1, t1, n+1, (ABool b)::l2))::stack)  
        | ( Cl (gamma , C i ) , OPCl(PROCTUPLE( m, h1::t1,  n, l2))::stack) -> execute( Cl(gamma, h1), OPCl(PROCTUPLE( m-1, t1, n+1, (AInt i)::l2))::stack)  
        (* I think last 2 cases can be unified *)
        
        | ( Cl (gamma, Def(vcll)) , stack) -> execute ( Cl(vcll@gamma, NExp ), stack )

        | _ -> raise MalformedExp

(* For Tuples or anything, make a tuple of closures, because the unit is NOT exp, it's closures *)