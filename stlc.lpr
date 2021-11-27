% A typechecker for the simply-typed lambda calculus.
typeof unit unit.
typeof (lam F) (fun A B) :- pi x\ (typeof x A => typeof (F x) B).
typeof (app F X) B :- typeof F (fun A B), typeof X A.
