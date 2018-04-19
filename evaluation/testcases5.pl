%variables
hasType([ typeVar(variable("X"), (int)) , typeVar(variable("Y"), int )], variable("X"), T).
hasType([ typeVar(variable("X"), (bool)), typeVar(variable("X"), int )], variable("X"), T).

%Constants
hasType([], const(-652), T).
hasType([], true, T).

%arithmetic
hasType([], add( sub(const(2), const(5)), div(const(6), mul(const(2), const(5)))), T).

%boolean
hasType([ typeVar(variable("X"), bool) ], and(impl(or(variable("X"), false), true), impl(variable("X"), not(false))), T).

%comparison
hasType([ typeVar(variable("X"), bool ), typeVar(variable("Y"), bool )], or(and(gt(const(-2), const(6)), lt(const(3), const(100))), impl(eql(const(5), variable("Y")), variable("X"))), T).

%equality
hasType([], eql( tuple([ tuple([const(1), const(3)]), true]),  tuple([const(1), const(3), true])), T).

%if then else
hasType([ typeVar(variable("X"), bool),  typeVar(variable("Y"), int)], ifte(and(variable("X"), gt(variable("Y"), 0)), variable("Y"), variable("X")), T).

%let d in e
hasType([ typeVar(variable("Y"), int)], letin( variable("X"), const(3), add(variable("Y"), variable("X"))), T).
hasType([ typeVar(variable(x), int)], letin( variable(y), const(3), mul(variable(y), const(5))), T).

%abstraction
hasType( [typeVar(variable(x), bool), typeVar(variable(w), bool)], lambda(variable(x), variable(w)), arrow( bool, bool )). 
hasType( [typeVar(variable(x), bool), typeVar(variable(w), bool)], lambda(variable(x), variable(w)), arrow( bool, bool )). 
% ^ p

%application
hasType([ typeVar(variable(r), arrow( bool, bool)), typeVar(variable(s), bool)], apply(variable(r), variable(s)), bool ).
hasType([ typeVar(variable(r), arrow( bool, bool)), typeVar(variable(s), bool), typeVar(variable(s), bool), (variable(r), arrow(bool , bool ))], apply(variable(r), variable(s)), X).


%n- tuple
hasType([ typeVar(variable(x), bool ),  typeVar(variable(w), bool )],  tuple([variable(x), variable(w), and(variable(x), variable(y))]), cartesianProduct([ bool,  bool]) ).

%projection
hasType([ typeVar(variable(y), bool ),  typeVar(variable(z), bool )], proj( const(1) ,tuple( [variable(x), variable(w), and(variable(x), variable(y)) ] )) , bool ).

%constructors
% hasType([ typeVar(variable(r), bool )] , inl(variable(r)), disjunction( bool ,  bool )).
% hasType([ typeVar(variable(r), bool )] , inl(variable(r)), X).
% hasType([ typeVar(variable(r), bool )] , inr(variable(r)), disjunction( bool ,  bool )).

%case analysis
% hasType([typeVar(variable(t), bool ), typeVar(variable(r), bool )], case(inl(variable(t)), variable(r)), bool ).
% hasType([typeVar(variable(t), bool ), typeVar(variable(r), bool )], case(inr(variable(t)), variable(r)), bool ).


%type elaborates

typeElaborates([], def(variable("X"), add( const(3), const(4) )), T).
typeElaborates([], def(variable("Y"), true), T).
typeElaborates([], pll(def(variable("X"), const(3)), def(variable("Y"), true)), T).
typeElaborates([], pll(def(variable("X"), const(3)), def(variable("X"), true)), T).
typeElaborates([], seq(def(variable("X"), mul( const(31), const(20) )), def(variable("Y"), true)), T).
typeElaborates([typeVar(variable("X"), bool), typeVar(variable("Y"), int)], 
				loc(
							def(variable("X"), const(31)), 
						 	pll(def(variable("X"),  tuple([variable("Y")])), def(variable("Y"), false))

						 ), T).

typeElaborates([typeVar(variable("X"), bool), typeVar(variable("Y"), int)], 
				loc(
							def(variable("X"), const(20)), 
						 	pll(def(variable("X"), const(3)), def(variable("Y"), false))

						 ), T).
typeElaborates([ typeVar(variable(x), int )],  def(variable(y), const(9)), Gamma).

typeElaborates([ typeVar(variable(x), int )], seq( def(variable(z), true ),  def(variable(y), false )), Gamma).

typeElaborates([ typeVar(variable(x), int )],  pll( def(variable(z), const(9)),  def(variable(y), const(0))), Gamma).

typeElaborates([ typeVar(variable(x), int )], loc( def(variable(z), const(9)),  def(variable(y), const(4))), Gamma).

typeElaborates([ typeVar(variable(x), int )],  pll(seq( def(variable(z), const(8)),  def(variable(y), true )),  def(variable(y), false )), Gamma).

typeElaborates([ typeVar(variable(x), int )], seq( pll( def(variable(z), const(45)),  def(variable(y), false )),  def(variable(y), const(8))), Gamma).
