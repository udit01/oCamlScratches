% move(N,X,Y,Z) - move N disks from peg X to peg Y, with peg Z being the
%                 auxilliary peg
%
% Strategy:
% Base Case: One disc - To transfer a stack consisting of 1 disc from 
%    peg X to peg Y, simply move that disc from X to Y 
% Recursive Case: To transfer n discs from X to Y, do the following: 
% Transfer the first n-1 discs to some other peg X 
% Move the last disc on X to Y 
% Transfer the n-1 discs from X to peg Y

% move(1,X,Y,_) :-  
% write('Move top disk from '), 
% write(X), 
% write(' to '), 
% write(Y), 
% nl. 
% move(N,X,Y,Z) :- 
% N>1, 
% M is N-1, 
% move(M,X,Z,Y), 
% move(1,X,Y,_), 
% move(M,Z,Y,X).  

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% likes(mary,food).
% likes(mary,wine).
% likes(john,wine).
% likes(john,mary).
% likes(tom,tom).
% likes(tilda, wine).
% % not(likes(john,john)).

% likes(john,X) :- likes(mary,X).
% likes(john,Y) :- likes(Y, wine).
% likes(john,Z) :- likes(Z,Z),Z = not(john).

% ORDERING MATTERS ? WHY ? john shouldn't like john anywhere , but he does somewhere, see the interpreter output on likes(john,X) query

male(james1).
male(charles1).
male(charles2).
male(james2).
male(george1).

female(catherine).
female(elizabeth).
female(sophia).

% a has parent b
parent(charles1, james1).
parent(elizabeth, james1).
parent(charles2, charles1).
parent(catherine, charles1).
parent(james2, charles1).
parent(sophia, elizabeth).
parent(george1, sophia).

% x has mother y
mother(X,Y) :- parent(X,Y),female(Y).
father(X,Y) :- parent(X,Y),male(Y).
sibling(X,Y):- dif(X,Y),parent(X,Z),parent(Y,Z).

% x has sister y
sister(X,Y) :- sibling(X,Y),female(Y).
brother(X,Y):- sibling(X,Y),male(Y).
% x has aunt y
aunt(X,Y) :- parent(X,Z),sister(Z,Y).
uncle(X,Y) :- parent(X,Z),brother(Z,Y).
% x has grandparent y
grandparent(X,Y) :- parent(X,Z),parent(Z,Y).
cousin(X,Y):- parent(X,Z),parent(Y,W),sibling(Z,W).
        % "sister", "brother", 
        % "aunt", "uncle", 
        % "grandparent", "cousin" 
