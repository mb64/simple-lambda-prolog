% Reverse a list.  A test for delaying non-pattern unification problems
% vim:ft=lprolog

append nil X X.
append (cons X Xs) Ys (cons X Zs) :- append Xs Ys Zs.

% type frev (list A -> list A) -> (list A -> list A) -> o.
frev (tl\ tl) (tl\ tl).
frev (tl\ cons X (F tl)) (tl\ G (cons X tl)) :- rev F G.

% type rev list A -> list A -> o.
rev Xs Ys :- (pi tl\ append Xs tl (F tl)), G nil = Ys, frev F G.

