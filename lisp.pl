:- set_prolog_flag(double_quotes, codes).

parse(String, Expr) :- phrase(lisp(Expr), String). % Parse lisp input to AST

/**
 * LISP grammar
 **/
lisp([Expr|Rest]) -->
    expression(Expr),
    space,
    lisp(Rest), !. % tail recursion
lisp([]) --> [].


% Whitespace separating expressions
space --> [S], { S =< 0' }, space. %'
space --> [].

% (((())))
parenthesis_start --> space, "(", space.
parenthesis_end --> space, ")", space.

expression(s(Symbol)) --> symbol(Literal), { name(Symbol, Literal) }. % Expression is a symbol
expression(n(Number)) --> number(Literal), { name(Number, Literal) }. % Expression is number literal
expression(List) --> list(List).
expression([s(quote),Q]) --> "'", expression(Q). %'

% Parse numbers, longest match wins
number([45 | N]) --> "-", numeral(N), !. % Negative numbers
number(N) --> numeral(N), !.

numeral([D | Rest]) --> digit(D), number(Rest).
numeral([101 | Rest]) --> "e", exponent(Rest).
numeral([46 | Rest]) --> ".", digits(Rest).
numeral([D]) --> digit(D).

exponent(Expt) --> digits(Expt).
exponent([45 | Expt]) --> "-", digits(Expt).

digits([D | Rest]) --> digit(D), digits(Rest).
digits([D]) --> digit(D).

digit(D) --> [D], { member(D, "0123456789") }.


% Parse symbols
symbol([Head | Tail]) --> % Symbol can't be empty
    \+(digit(Head)), % Mustn't start with a digit
    symbol_rest([Head | Tail]),
    !. % Longest wins

symbol_rest([Head|Tail]) -->
    [Head], { member(Head, "+/-*><=abcdefghijklmnopqrstuvwxyz0123456789") },
    symbol_rest(Tail).
symbol_rest([]) --> [].

% Parse lists (1 (1 2 3) 3)
list(Expr) --> parenthesis_start, lisp(Expr), parenthesis_end.

/**
 * LISP interpreter
 **/

% Transform typed symbols to lispy variables
uncompile([H0], [H1]) :- uncompile(H0, H1), !.
uncompile([H0 | T0], [H1 | T1]) :- uncompile(H0, H1),uncompile(T0, T1), !.
uncompile([], []) :- !.
uncompile(s(quote), "'"). %'
uncompile(s(Symbol), Symbol).
uncompile(n(N), N).
uncompile(true, true).


run(String, Result) :-
  empty_assoc(E),
  run(String, E, _, Results),
  last(Results, Result), !.

run(String, E0, E1, Result) :-
  parse(String, Expressions),
  eval_all(Expressions, E0, R0, E1),
  maplist(uncompile, R0, Result),
  !.


:- dynamic eval/4. % Assert/retract for function resolvation

% Evaluate all expressions
eval_all([H|T], E0, [V | Values], E2) :-
  eval(H, E0, V, E1),
  eval_all(T, E1, Values, E2).
eval_all([], E0, [], E0).

% Empty list
eval([], E, [], E).

eval(n(Number), E, n(Number), E). % Identity

% Nil symbol
eval(s(nil), E, [], E).

% Other symbols
eval(s(Symbol), E, R, E) :-
  get_assoc(s(Symbol), E, R). % Lookup variable from symbol table

% Quote
eval([s(quote) | [Arguments]], E, Arguments, E).

% Defun
eval([s(defun), Name, Arguments, Body], E0, Name, E1) :-
  put_assoc(f(Name), E0, [Arguments, Body], E1), !.

% If - then
eval([s(if), Cond, Then,  _], E0, Value, E2) :-
  eval(Cond, E0, R, E1),
  \+ falsy(R),
  eval(Then, E1, Value, E2).
% If - else
eval([s(if), Cond , _ , Else], E0, Value, E2) :-
    eval(Cond, E0, [], E1),
    eval(Else, E1, Value, E2).

% Evaluation of predefined functions
eval([Function | Arguments], E0, Result, E3) :-
  eval_all(Arguments, E0, Values, E1),
  asserta(eval(s(A), B, A, B)),
  eval(Function, E1, F0, E2),
  retract(eval(s(A), B, A, B)),
  apply(F0, Values, E2, Result, E3), !.

% Evaluation of user defined functions
eval([Function | Arguments], E0, Result, E0) :-
  eval_all(Arguments, E0, Values, E1),
  asserta(eval(s(A), B, A, B)),
  eval(Function, E1, F0, E2),
  retract(eval(s(A), B, A, B)),
  apply(f(s(F0)), Values, E2, Result, _).


falsy([]).

% Math
apply(+, Arguments, E, Sum, E) :- sumlist(Arguments, Sum).
apply(-, [n(Head) | Tail], E, n(Sum), E) :-
  sumlist(Tail, n(Minuses)),
  Sum is Head - Minuses.
apply(*, Arguments, E, Product, E) :- productlist(Arguments, Product).
apply(/, [n(Head) | Tail], E, n(Result), E) :-
  productlist(Tail, n(Divident)),
  Divident \= 0,
  Result is Head / Divident.
  
% <
apply(<, [n(A), n(B)], E, true, E) :- <(A, B).
apply(<, [n(A), n(B)], E, [], E) :- >=(A, B).

% >
apply(>, [n(A), n(B)], E, true, E) :- >(A, B).
apply(>, [n(A), n(B)], E, [], E) :- =<(A, B).

% eval
apply(eval, [Arguments], E0, Result, E1) :-
  eval(Arguments, E0, Result, E1).

% apply
apply(apply, [Fun | [Arguments]], E0, Result, E2) :-
  eval([Fun | Arguments], E0, Result, E2).

% not
apply(not, [[]], E, true, E) :- !.
apply(not, [_], E, [], E).

% eq
apply(eq, [A, A], E, true, E) :- !.
apply(eq, [_, _], E, [], E).

% car
apply(car, [[Head | _]], E, Head, E).

% cdr
apply(cdr, [[_ | Tail]], E, Tail, E).

% atom
apply(atom, [n(A)], E, true, E) :- atomic(A).
apply(atom, [A], E, true, E) :- atomic(A).
apply(atom, [A], E, [], E) :- \+ atomic(A).

% numberp
apply(numberp, [n(A)], E, true, E) :- number(A).
apply(numberp, [n(A)], E, [], E) :- \+ number(A).

% cons
apply(cons, [Head, Tail], E, [Head | Tail], E).

% progn
apply(progn, [_ | Rs], E, R, E) :-
  apply(progn, Rs, E, R, E).
apply(progn, [R], E, R, E).

% set
apply(set, [Symbol, Value], E0, Value, E1) :-
  put_assoc(Symbol, E0, Value, E1).

% User defined functions
apply(f(Function), Arguments, E0, R, E0) :-
  get_assoc(f(Function), E0, [Names, Body]),
  bind_environment(Arguments, Names, E0, E1),
  apply(eval, [Body], E1, R, _).

% Bind variables to environment
bind_environment([Value | T0], [Name | T1], E0, E2) :-
  put_assoc(Name, E0, Value, E1),
  bind_environment(T0, T1, E1, E2).
bind_environment([], [], E, E).

% Helper rules for math
sumlist(L,Sum) :-
  sumlist(L,0,Sum).

sumlist([],Sum,n(Sum)).
sumlist([n(H)|T],Count,Sum) :-
  NewCount is Count + H,
  sumlist(T,NewCount,Sum).

productlist(L, Product) :-
  productlist(L, 1, Product).

productlist(_, 0, 0) :- !. % Optimize!
productlist([], Product, n(Product)).
productlist([n(H)|T], Count, Product) :-
  NewCount is Count * H,
  productlist(T, NewCount, Product).

last([_|T], L) :- last(T, L).
last([H], H).
