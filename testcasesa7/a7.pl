% Here are the test cases for assignment 7.

% member(X,[X| _]).
% member(X,[_ |T]) :- member(X,T).

% ?- member(2,[1,2,3,4]).

% length([], 0).
% length([A|B],N) :- length(B,M), N is M+1 .

% ?- length([2,3,4,5],W).

% intersection([],X,[]).
% intersection([X|R],Y,[X|Z]) :- member(X,Y), !, intersection(R,Y,Z).
% intersection([X|R],Y,Z) :- intersection(R,Y,Z).

% ?- intersection([a,e,i],[o,u],L).
% ?- intersection([s,u,m],[r,s,m],L).

likes(joe,books).
likes(joe,mary).
likes(mary,books).
likes(john,books).
likes(sue,joe).
likes(john,mary).
likes(mary,joe).
likes(mary,movies).
likes(bill,X) :- likes(X,books), likes(X,movies).
likes(alice,X) :- likes(X,mary).

?- likes(bill,joe).
?- likes(alice,mary).

ancestor(bob, susan).
ancestor(A, X) :- parent(A, X).
ancestor(A, X) :- parent(A, C), ancestor(C, X).
parent(fred, sally).
parent(tina, sally).
parent(sally, john).
parent(sally, diane).
parent(sam, bill).

?- ancestor(tina,W).
?- ancestor(fred,john).