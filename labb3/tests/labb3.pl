% Load model, initial state and formula from file.
verify(Input) :- 
    see(Input), 
    read(T), % T - The transitions in form of adjacency lists
    read(L), % L - The labeling
    read(S), % S - Current state 
    read(F), % F - CTL Formula to check
    seen, 
    check(T, L, S, [], F),!.

% check(T, L, S, U, F) % U - Currently recorded states

% X true for all
checkA(_, _, [], _, _).
checkA(T, L, [S|Tail], U, X) :- 
    check(T, L, S, U, X), 
    checkA(T, L, Tail, U, X).

% X true for some 
checkE(T, L, [S|Tail], U, X) :- 
	check(T, L, S, U, X); 
	checkE(T, L, Tail, U, X).

% P
check(_, L, S, [], X) :- 
    member([S,Tail], L), 
    member(X, Tail).

% Neg(P)
check(_, L, S, [], neg(X)) :- 
    \+check(_, L, S, [], X).

% And
check(T, L, S, [], and(X,Y)) :- 
    check(T, L, S, [], X), 
    check(T, L, S, [], Y).

% Or
check(T, L, S, [], or(X,Y)) :- 
    check(T, L, S, [], X); 
    check(T, L, S, [], Y).

% AX
check(T, L, S, [], ax(X)) :- 
    member([S,Tail], T),
    checkA(T, L, Tail, [], X).

% EX
check(T, L, S, [], ex(X)) :- 
    member([S,Tail], T),
    checkE(T, L, Tail, [], X).

% AG1
check(_, _, S, U, ag(_)) :- member(S, U).
% AG2
check(T, L, S, U, ag(X)) :- 
    \+member(S, U),
    check(T, L, S, [], X),
    member([S, Tail], T),
	checkA(T, L, Tail, [S|U], ag(X)).

% EG1
check(_, _, S, U, eg(_)) :- member(S, U).
% EG2 
check(T, L, S, U, eg(X)) :- 
    \+member(S, U),
    check(T, L, S, [], X),
    member([S, Tail], T),
	checkE(T, L, Tail, [S|U], eg(X)).

% AF1
check(T, L, S, U, af(X)) :- 
    \+member(S, U), 
    check(T, L, S, [], X).
% AF2 
check(T, L, S, U, af(X)) :-
	\+member(S, U),
	member([S, Tail], T),
	checkA(T, L, Tail, [S|U], af(X)).

% EF1
check(T, L, S, U, ef(X)) :- 
    \+member(S, U), 
    check(T, L, S, [], X).
% EF2 
check(T, L, S, U, ef(X)) :-
    \+member(S, U), 
    member([S, Tail], T), 
    checkE(T, L, Tail, [S|U], ef(X)).
