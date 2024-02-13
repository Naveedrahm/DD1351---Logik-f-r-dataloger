verify(InputFileName) :- see(InputFileName),
    read(Prems), read(Goal), read(Proof),
    seen,
    valid_proof(Prems, Goal, Proof).

valid_proof(Prems, Goal, Proof):-
    check_goal(Goal,Proof),
    check_proof(Prems,Proof,[]), !.

check_goal(Goal,Proof):-
    last(Proof,LastRow),
    nth1(2,LastRow,Goal).

addList(H,CheckedList,NewList):-
    appendEl(H,CheckedList,NewList).

appendEl(X,[],[X]).
appendEl(X,[H|T],[H|Y]):-
    appendEl(X,T,Y).

check_proof(_,[],_).
check_proof(Prems,[H|T],CheckedList):-
    check_rule(Prems,H,CheckedList),
    addList(H,CheckedList,NewList),
    check_proof(Prems,T,NewList).    

%premise
check_rule(Prems,[_,X, premise],_):-
    member(X,Prems).

%andint
check_rule(_,[_,and(X,Y),andint(A,B)],CheckedList):-
    member([A,X,_],CheckedList),
    member([B,Y,_],CheckedList).

%andel1
check_rule(_,[_,X,andel1(A)],CheckedList):-
    member( [A,and(X,_),_], CheckedList).

%andel2
check_rule(_,[_,X,andel2(A)],CheckedList):-
    member([A,and(_,X),_], CheckedList).

%orint1
check_rule(_,[_,or(X,_),orint1(A)],CheckedList):-
    member([A,X,_],CheckedList).

%orint2
check_rule(_,[_,or(_,X),orint2(A)],CheckedList):-
    member([A,X,_],CheckedList).

%orel?
check_rule(_, [_, X, orel(A,B,C,D,E)], CheckedList) :- 
    member([A, or(Y, Z), _], CheckedList),
	member(Box1, CheckedList), member(Box2, CheckedList),
	member([B, Y, assumption], Box1), last(Box1, Last1), Last1 = [C, X, _],
	member([D, Z, assumption], Box2), last(Box2, Last2), Last2 = [E, X, _].

%impint?
check_rule(_, [_, imp(X, Y), impint(A,B)], CheckedList) :- 
    member(Box, CheckedList),
	member([A, X, assumption], Box),
	last(Box, Last),
	Last = [B, Y, _].

%impel
check_rule(_,[_,X,impel(A,B)],CheckedList):-
    member([A,Y,_],CheckedList),
    member([B,imp(Y,X),_], CheckedList).

%negint?
check_rule(_, [_, neg(X), negint(A,B)], CheckedList) :- 
    member(Box, CheckedList),
	member([A, X, assumption], Box),
    last(Box, Last),
	Last = [B, cont, _].

%negel
check_rule(_,[_,cont,negel(A,B)], CheckedList):-
    member([A,X,_], CheckedList),
    member([B,neg(X),_], CheckedList). 

%contel
check_rule(_,[_,_,contel(A)],CheckedList):-
    member([A,cont,_],CheckedList).

%negnegint
check_rule(_,[_,neg(neg(X)), negnegint(A)], CheckedList):-
    member([A,X,_], CheckedList).

%negnegel
check_rule(_,[_,X, negnegel(A)], CheckedList):-
    member([A,neg(neg(X)),_], CheckedList).

%copy
check_rule(_,[_,X,copy(A)],CheckedList):-
    member([A,X,_],CheckedList).

%mt
check_rule(_,[_,neg(X),mt(A,B)],CheckedList):-
    member([A,imp(X,Y),_],CheckedList),
    member([B,neg(Y),_],CheckedList).

%pbc
check_rule(_, [_, X, pbc(A,B)], CheckedList) :- 
    member(Box, CheckedList),
	member([A, neg(X), assumption], Box),
	last(Box, Last),
	Last = [B, cont, _].

%lem
check_rule(_,[_,or(X,neg(X)),lem],_).

%box
check_rule(Prems, [[A, _, assumption]|Box], CheckedList) :- check_proof(Prems, Box, [[A, _, assumption]|CheckedList]).