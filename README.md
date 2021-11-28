# A λProlog interpreter

Features:
 - Pattern unification
 - `sigma`, `pi`, and hypothetical clauses
 - A mediocre REPL

Unimplemented features:
 - Delaying constraints (SWI Prolog `freeze/2`, ELPI `declare_constraint`)
 - Typechecking
 - A good REPL

## An example that works right now

```prolog
% stlc.lpr
% A typechecker for the simply-typed lambda calculus.
typeof unit unit.
typeof (lam F) (fun A B) :- pi x\ (typeof x A => typeof (F x) B).
typeof (app F X) B :- typeof F (fun A B), typeof X A.
```

Compile and run with

```prolog
$ ocamlfind ocamlc -package angstrom -package stdio -linkpkg -g -o lp lp.ml
$ ./lp stlc.lpr
Loaded stlc.lpr
?- typeof (lam f\ app f unit) T, T = fun _ a. % It can typecheck!
yes.
 T = fun (fun unit a) a
?- typeof Code (fun unit unit). % It can synthesize code!
yes.
 Code = lam (x₀\ x₀)
```

