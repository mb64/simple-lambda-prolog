# A λProlog interpreter

Features:
 - Pattern unification
 - `sigma`, `pi`, and hypothetical clauses
 - A mediocre REPL

Unimplemented features:
 - Delaying constraints (SWI Prolog `freeze/2`, ELPI `declare_constraint`)
 - Typechecking
 - A good REPL
 - All the full lambda prolog connectives (`&`, conjunctions in hypotheticals,
   custom operators)

Known bugs:
 - Flexible goals aren't implicitly `call`'d, so if you pass a cut as a
   first-class goal it will actually cut


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
$ make
$ ./lp stlc.lpr
Loaded stlc.lpr
?- typeof (lam f\ app f unit) T, T = fun _ a. % It can typecheck!
yes.
 T = fun (fun unit a) a
more? 
?- typeof Code (fun unit unit). % It can synthesize code!
yes.
 Code = lam (x₀\ x₀)
more? y
yes.
 Code = lam (x₀\ unit)
more? 
?- :quit
$ 
```

## Architectural notes

**Term representation**

The data representation uses call-by-value normalization by evaluation.  What
this means practically is that contants (either global or introduced by
`pi x\ ...`) are given de Bruijn levels, while variables bound inside a term are
represented with de Bruijn indices, and substitution under binders is done
lazily.  (I've stolen ELPI's trick of giving global constants negative de Bruijn
levels.)  AFAICT Teyjus is similar, except call-by-need instead of
call-by-value (and it doesn't use the framework of NbE).

While NbE is efficient for typecheckers where you frequently inspect the top
layer of the type, I expect it's less efficient when literally every operation
is unification, which does full normalization.  If I reimplement it I will
switch to 100% de Bruijn levels, like ELPI and Makam.  (Although maybe NbE would
be good for a λMercury kinda thing, where there's little to no actual
unification...)

**Unification variables**

The handling of unification variables is pretty standard, but that standard
isn't clearly documented anywhere I know of so it's maybe worth explaining.

The scope of a unification variable comes from two sources:

1. With *strongly scoped unification variables*, each unification variable lives
   at a particular level, indicating its scope.  In my code, a unification
   variable at level `scope` may only refer to constants with level `lvl < scope`
   (or other unification variables at level `scope' <= scope`).  *(Note: this
   `<`/`<=` asymmetry is kinda weird but ELPI uses this convention too, so
   whatever)*

   This relates to a "mixed prefix", where you consider a unification problem as
   an equation under mixed forall and exists quantifiers:
   `∀ c₀ ∀ c₁ ∃ X ∀ c₂ ∃ Y (this = that)`.  Here, `X` would be at level `2`,
   unable to refer to `c₂` in its solution.

2. What's the normal form of `X a`, when `X` is a free logic variable?  There's
   two options here:
    - You could try to beta-reduce, solving `X` as `λx. Y` and evaluating the
      expression to `Y [a / x]`.  However, you can't simplify that any further,
      so you're now forced to add explicit subtitutions into the term language.

    - You could instead decide that `X a` *is* its normal form, at least until
      `X` is solved.

   No implementation that I know of chooses the first option, presumably since
   it adds extra things to worry about (explicit subtitutions) without much
   gain.

   The consequence of having `X a` be a normal form is that the base case of
   unification now has to consider instantiating a logic variable *applied to
   some arguments*, rather than just a logic variable on its own.  In pattern
   unification problems, these arguments act like bonus items in its scope.

**Clause selection**

Nothing special is done here.  Global clauses are stored in a global hashmap,
and local clauses are passed around in the `ctx` record.

In particular, clause matching is done in the dumbest possible way: every clause
for a predicate is tried (no indexing), performing full unification on the
arguments.

**Backtracking evaluation**

The runtime is written in a double-barrelled CPS style, passing around a success
continuation `sk` and a failure continuation `fk`.

