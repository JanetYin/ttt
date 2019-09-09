# Meta

You can take semi-compulsory courses in later semesters.

Tutorials:

1. Kaposi Ágoston
2. Kovács András
3. Rafaël Bocquet (English)

Requirements:

 * Canvas quiz for each lecture
 * At the beginning of each tutorial a small assignment in the bead
   system. Weekly homeworks in the same system help preparing.
 * Exam on the computer during the exam period.

For the tutorial, you get the following marks according to how many
assignments you completed (out of 10, for each assignment you can get
0 or 1 points): 5-6: 2, 7: 3, 8: 4, 9-10: 5

To enter the exam, you need 50% in Canvas quizes and a minimum 2 mark
for the tutorial.

Recommended literature:

* [Thorsten Altenkirch. Naive Type Theory](http://www.cs.nott.ac.uk/~psztxa/publ/fomus19.pdf)
* [Homotopy Type Theory book](http://saunders.phil.cmu.edu/book/hott-online.pdf) (especially Chapter 1 Type theory)
* [Philip Wadler. Programming Language Foundations in Agda](https://plfa.github.io/)
* [Kaposi Ambrus. Bevezetés a homotópia-típuselméletbe](https://akaposi.github.io/hott_bevezeto.pdf) (magyar)
* [Martin Hofmann. Syntax and Semantics of Dependent Types](https://www.tcs.ifi.lmu.de/mitarbeiter/martin-hofmann/pdfs/syntaxandsemanticsof-dependenttypes.pdf)

# Intro

`t : A`

t is a term (program), A is its type

examples: `(1 + 1) : ℕ`, `(λ b → if b then 1 else 3) : Bool → ℕ`

Sometimes type theory means the study of type systems for programming
languages. Here we study Martin-Löf's type theory. This is a
programming language and a foundation of mathematics.

It can be used as a replacement for set theory. Differences.

`x ∈ A` in set theory is a proposition, while `t : A` is a judgement
(analogy: static and dynamic type systems: Haskell vs Python). `1 + 1 =
2` is at a different level from `(1 + 1) : ℕ`, but in set theory `(1 + 1) ∈
ℕ` is a proposition too. Representation independence in type theory, we
cannot ask `2 ∈ 3` or `Bool ∩ ℕ = ∅`.

We define a programming language by listing all the ways to construct
programs of different types and equalities which explain how programs
run.

# Simple type theory

Rules, constructing programs with it

Booleans

Natural numbers

Product

Sum

Functions

# Some propositional logic

Maybe talk about Curry-Howard?

# Indexed types

Vectors
Equality

# Predicate logic

do some discrete math

