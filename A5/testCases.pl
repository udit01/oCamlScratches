hasType( G, true , T ).
hasType(G, and(A,B) , T).
hasType(G, and(A,B) , T).
hasType(G, pow(A,B) , T).
hasType(G, const(A) , T).

hasType(G, and(A,B) , T).
hasType(G, eql(A,B) , T).

typeElaborates( [] , def(variable(X), add(const(3),const(5))), Gn).
