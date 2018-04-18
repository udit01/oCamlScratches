%variables
hastype([(variable("X"),typevar(intT)),(variable("Y"),typevar(intT))],variable("X"),T).
hastype([(variable("X"),typevar(boolT)),(variable("X"),typevar(intT))],variable("X"),T).

%Constants
hastype([],-652,T).
hastype([],true,T).

%arithmetic
hastype([],add(subtract(2,5), divide(6,multiply(2,5))),T).

%boolean
hastype([(variable("X"),typevar(boolT))],and(implies(or(variable("X"), false), true),implies(variable("X"), not(false))),T).

%comparison
hastype([(variable("X"),typeVar(boolT)),(variable("Y"),typeVar(boolT))],or(and(greater(-2, 6), less(3,100)),implies(equals(5, variable("Y")), variable("X"))),T).

%equality
hastype([],equals(tup([tup([1,3]),true]),tup([1, 3,true])),T).

%if then else
hastype([(variable("X"),typevar(boolT)),(variable("Y"),typevar(intT))],if_then_else(and(variable("X"),greater(variable("Y"),0)),variable("Y"),variable("X")),T).

%let d in e
hastype([(variable("Y"),typevar(intT))],let_in_end(def(variable("X"),3),add(variable("Y"),variable("X"))),T).
hasType([(variable(x),typeVar(intT))],let_in_end(simple_def(variable(y),const(3)),mul(variable(y),const(5))),T).

%abstraction
hastype( [(variable(x), typeVar(boolT)), (variable(w), typeVar(boolTT))], lambda(variable(x), variable(w)), arrow(typeVar(boolT), typeVar(boolT))). 
hastype( [(variable(x), typeVar(boolT)), p(variable(w), typeVar(boolT))], lambda(variable(x), variable(w)), arrow(typeVar(boolT), typeVar(boolT))). 

%application
hastype([(variable(r), arrow(typeVar(boolT),typeVar(boolT))), (variable(s), typeVar(boolT))], app(variable(r), variable(s)), typeVar(boolT)).
hastype([(variable(r), arrow(typeVar(boolT),typeVar(boolT))), (variable(s), typeVar(boolT)), (variable(s), typeVar(boolT)), (variable(r), arrow(typeVar(boolT),typeVar(boolT)))], app(variable(r), variable(s)), X).


%n-tuple
hastype([(variable(x), typeVar(boolT)), (variable(w), typeVar(boolT))], tuple(variable(x), variable(w), and(variable(x), variable(y))), conjunction(typeVar(boolT), typeVar(boolT))).

%projection
hastype([(variable(y), typeVar(boolT)), (variable(z), typeVar(boolT))], proj(tuple(variable(x), variable(w), and(variable(x), variable(y))) 1), typeVar(boolT)).

%constructors
hastype([(variable(r), typevar(boolT))] ,inl(variable(r)), disjunction(typevar(boolT),typevar(boolT))).
hastype([(variable(r), typevar(boolT))] ,inl(variable(r)), X).
hastype([(variable(r), typevar(boolT))] ,inr(variable(r)), disjunction(typevar(boolT),typevar(boolT))).

%case analysis
hastype([(variable(t), typevar(boolT)), (variable(r), typevar(boolT))], case(inl(variable(t)), variable(r)), typevar(boolT)).
hastype([(variable(t), typevar(boolT)), (variable(r), typevar(boolT))], case(inr(variable(t)), variable(r)), typevar(boolT)).


%type elaborates

typeElaborates([],def(variable("X"),add(3,4)),T).
typeElaborates([],def(variable("Y"),true),T).
typeElaborates([],parallel(def(variable("X"),3),def(variable("Y"),true)),T).
typeElaborates([],parallel(def(variable("X"),3),def(variable("X"),true)),T).
typeElaborates([],sequential(def(variable("X"),mul(31,20)),def(variable("Y"),true)),T).
typeElaborates([(variable("X"),boolT),(variable("Y"),intT)],
				localdef(
							def(variable("X"),31),
						 	parallel(def(variable("X"),tup([variable("Y")])),def(variable("Y"),false))

						 ),T).

typeElaborates([(variable("X"),boolT),(variable("Y"),intT)],
				localdef(
							def(variable("X"),20),
						 	parallel(def(variable("X"),3),def(variable("Y"),false))

						 ),T).
typeElaborates([(variable(x),typeVar(intT))],simple_def(variable(y),const(9)),Gamma).

typeElaborates([(variable(x),typeVar(intT))],sequential_def(simple_def(variable(z),constb(true)),simple_def(variable(y),constb(false))),Gamma).

typeElaborates([(variable(x),typeVar(intT))],parallel_def(simple_def(variable(z),const(9)),simple_def(variable(y),const(0))),Gamma).

typeElaborates([(variable(x),typeVar(intT))],local_def(simple_def(variable(z),const(9)),simple_def(variable(y),const(4))),Gamma).

typeElaborates([(variable(x),typeVar(intT))],parallel_def(sequential_def(simple_def(variable(z),const(8)),simple_def(variable(y),constb(true))),simple_def(variable(y),constb(false))),Gamma).

typeElaborates([(variable(x),typeVar(intT))],sequential_def(parallel_def(simple_def(variable(z),const(45)),simple_def(variable(y),constb(false))),simple_def(variable(y),const(8))),Gamma).
