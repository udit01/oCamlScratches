% In this assignment, you will write a type-checker for a simple functional language.
%  You need to write a Prolog predicate hastype(Gamma, E, T), where 
%     Gamma is a list of variable-type pairs, representing type assumptions on variables
%     E is an object language expression, 
%     T is a type.

% This predicate is mutually recursively defined with another Prolog predicate

%  typeElaborates(Gamma, D, Gamma')
% where D is a definition.

% E ranges over (at least)
%     variables, modelled as say variable(X)
%     constants, both numerical and boolean (at least)
%     arithmetic operations over numerical expressions
%     boolean operations over boolean expressions
%     comparison operations over numerical expressions
%     equality over arbitrary expressions, where equality can be decided
%     conditional expressions if_then_else
%     qualified expressions of the form let D in E end
%     function abstractions \X.E  with functions as first-class citizens
%     function application (E1 E2)  
%     n-tuples  (n >= 0)
%     expressions using projection operations.
%     ....possible extensions to constructors, and case analysis expressions

% and 
% D ranges over (at least)
%     simple definitions X =def= E
%     sequential definitions D1; D2
%     parallel definitions D1 || D2
%     local definitions local D1 in D2 end
%     ... possible extension to recursive definitions

% and 
% T ranges over (at least)
%     Type variables modelled as say TypeVar(A) 
%     Base types intT, boolT, ...
%     Arrow types T1 -> T2 |
%     cartesian product types T1 * ... * Tn  (n>1)
%     ... possible extension to union types and recursive types...
% --
% You will  need to define suitable constructors for expressions, definitions, types, etc.
% You need to provide enough test examples to show your type checker works correctly. 
% --
% Note that this checker can work as a type inference engine.  However it does not work for polymorphic type inference. 
%  Show with counter-examples that this is the case. Like Eql is polymorphic ?
% --


% variable(X) .
% cartesian(T1, T2).
% arrow(T1, T2).
% pair(E1, E2).
% lookup(Gamma, variable(X), T) :- %parse the list recrusively

%appending lists recursively
% directly use constructors, no need for above ?

% gamma is a list of def(variable, Type)
lookup( [] , variable(X), T) :- fail. % What and why ?
lookup( [ vtype( variable(X), Type) | TL ], variable(X), Type ) :- !. %What's that ?
lookup( [ vtype( variable(Y), Type) | TL ], variable(X), T ) :-dif(X,Y) , lookup(TL, variable(X), T ) .

hasType(Gamma, variable(X), T) :- lookup(Gamma, variable(X), T).

% do all the same for float ?
hasType( _ , true , bool) .
hasType( _ , false , bool) .
hasType(Gamma, not(B) , bool) :- hasType(Gamma, B, bool) .
hasType(Gamma, or(E1,E2)  , bool) :- hasType(Gamma, E1, bool) , hasType(Gamma, E2, bool).
hasType(Gamma, and(E1,E2) , bool) :- hasType(Gamma, E1, bool) , hasType(Gamma, E2, bool).
hasType(Gamma, xor(E1,E2) , bool) :- hasType(Gamma, E1, bool) , hasType(Gamma, E2, bool).
hasType(Gamma, impl(E1,E2), bool) :- hasType(Gamma, E1, bool) , hasType(Gamma, E2, bool).

hasType(  _  , const(_)  , int) .
hasType(Gamma, abs(E)    , int) :- hasType(Gamma, E , int).
hasType(Gamma, add(E1,E2), int) :- hasType(Gamma, E1, int) , hasType(Gamma, E2, int).
hasType(Gamma, sub(E1,E2), int) :- hasType(Gamma, E1, int) , hasType(Gamma, E2, int).
hasType(Gamma, mul(E1,E2), int) :- hasType(Gamma, E1, int) , hasType(Gamma, E2, int).
hasType(Gamma, div(E1,E2), int) :- hasType(Gamma, E1, int) , hasType(Gamma, E2, int).
hasType(Gamma, mod(E1,E2), int) :- hasType(Gamma, E1, int) , hasType(Gamma, E2, int).
hasType(Gamma, pow(E1,E2), int) :- hasType(Gamma, E1, int) , hasType(Gamma, E2, int).
hasType(Gamma, max(E1,E2), int) :- hasType(Gamma, E1, int) , hasType(Gamma, E2, int).
hasType(Gamma, min(E1,E2), int) :- hasType(Gamma, E1, int) , hasType(Gamma, E2, int).
hasType(Gamma, eql(E1,E2), int) :- hasType(Gamma, E1, int) , hasType(Gamma, E2, int).
hasType(Gamma, div(E1,E2), int) :- hasType(Gamma, E1, int) , hasType(Gamma, E2, int).

% eql not working as expected
hasType(Gamma, eql(E1,E2), bool) :- hasType(Gamma, E1, bool), hasType(Gamma, E2,bool).    
hasType(Gamma, eql(E1,E2), bool) :- hasType(Gamma, E1, int) , hasType(Gamma, E2, int).
hasType(Gamma, gt(E1,E2) , bool) :- hasType(Gamma, E1, int) , hasType(Gamma, E2, int).
hasType(Gamma, lt(E1,E2) , bool) :- hasType(Gamma, E1, int) , hasType(Gamma, E2, int).
hasType(Gamma, gte(E1,E2), bool) :- hasType(Gamma, E1, int) , hasType(Gamma, E2, int).
hasType(Gamma, lte(E1,E2), bool) :- hasType(Gamma, E1, int) , hasType(Gamma, E2, int).

%n tuple of variable size
hasType(  _  , tuple([]), cartesianProduct([])).
hasType(Gamma, tuple([E]),cartesianProduct([T])) :- hasType(Gamma, E, T).
hasType(Gamma, tuple( [Head | Tail ]) , cartesianProduct([ TypeHead | TypeTail])) :- hasType(Gamma, Head, TypeHead), hasType(Gamma, tuple(Tail), cartesianProduct(TypeTail)) .

hasType(Gamma, ifte(E0, E1, E2) , T) :- hasType(Gamma, E0, bool), hasType(Gamma, E1, T), hasType(Gamma, E2, T).
hasType(Gamma, letin(variable(X), E1, E2), T2 ):-hasType(Gamma, E1, T1), hasType([ vtype(variable(X),T1) | Gamma], E2, T2) . % is this appropirate ?
hasType(Gamma, proj(const(0) , tuple([HD|TL])), T ) :-hasType(Gamma, HD, T ), !.
hasType(Gamma, proj(const(N) , tuple([HD|TL])), T ) :- K is N-1,  hasType(Gamma, proj(const(K), tuple(TL)), T ).
% hasType(Gamma, proj(n , tuple([HD|TL])), T ) :- dif(n,0) , hasType(Gamma, proj(n-1, tuple(TL)), T ).

hasType(Gamma, pair(E1, E2), cartesian(T1, T2)) :- hasType(Gamma, E1, T1), hasType(Gamma, E2, T2).

% hasType(Gamma, lambda(variable(X), E1), arrow(T1,T2)) :- hasType( [vtype(variable(X), T1) | Gamma] , E1, T2 ).
% Does the below line extract the list form gamma, or append to it ??
hasType(Gamma, lambda(variable(X), E1), arrow(T1,T2)) :- hasType( [ vtype(variable(X), T1) | Gamma ], E1, T2 ).
hasType(Gamma, apply(E1, E2), T) :- hasType(Gamma, E2, I),hasType(Gamma, E1, arrow(I,T)).


% type inference
% hasType(Gamma, E1, T1) :- hasType( [ vtype(X, T1) | Gamma], E2, T2).
%%%%%%%%%%%HOW TO DO THE POSSIBLE, EXTENSIONS TO CONSTRUCTORS ..... CASE ANALYSIS .... FLOATS?

%%%%%%%%%%% HOW TO DO RECURSIVE DEFINITIONS.

% why if below ? just concatenate ?
% typeElaborates
append([],X,X).                            
append([X|Y],Z,[X|W]) :- append(Y,Z,W).  

% intersection([], _, []).
% intersection([H1|T1], L2, [H1|Res]) :-    member(H1, L2),    intersection(T1, L2, Res).
% intersection([_|T1], L2, Res) :-    intersection(T1, L2, Res).


% typeElaborates(Gamma, def(variable(X),E) , append(vtype(variable(X),E),Gamma)).

% typeElaborates(Gamma, def(variable(X),E) , GammaNew) :- append( [vtype(variable(X),E)],Gamma, GammaNew).
typeElaborates(Gamma, def(variable(X),E) , [vtype(variable(X),T)]) :- hasType(Gamma, E, T).

%:- append( [vtype(variable(X),E)],Gamma, GammaNew).
typeElaborates(Gamma, seq(D1, D2), GammaNew) :- typeElaborates(Gamma, D1, G1),append(G1,Gamma,G2), typeElaborates(G2, D2, GammaIncr), append(GammaIncr,G2, GammaNew).

% typeElaborates(Gamma, pll(def(variable(X),_), def(variable(X),_)), GammaNew ) :- !.
typeElaborates(Gamma, pll(def(variable(X),E1), def(variable(Y),E2)), GammaNew) :- dif( X, Y ), % after this, as if seq
                                                                                typeElaborates(Gamma, def(variable(X),E1), G1),
                                                                                typeElaborates(Gamma, def(variable(Y),E2), G2),
                                                                                append(G1, Gamma, Gpr),
                                                                                append(G2, Gpr, GammaNew).

typeElaborates(Gamma, loc(D1, D2), GammaNew) :- typeElaborates(Gamma, D1, G1),append(G1, Gamma, Gtemp), typeElaborates(Gtemp, D2, Gincr),append(Gincr,Gamma ,GammaNew).
%:- typeElaborates()