# Meta

You can take semi-compulsory courses in later semesters.

You have to register with the correct code:

* BSc: IP-18KVSZTME
* MSc: IPM-18sztKVTEE
* MSc evening course: IPM-18EsztKVTEE

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
functional programming language and a foundation of mathematics at the
same time.

It can be used as a replacement for set theory. Differences:

* `x ∈ A` in set theory is a proposition, while `t : A` is a judgement
  (analogy: static and dynamic type systems: Haskell vs Python). In
  type theory, `1 + 1 = 2` is at a different level from `(1 + 1) : ℕ`,
  but in set theory `1 + 1 = 2` and `(1 + 1) ∈ ℕ` are both
  propositions. Representation independence in type theory, we cannot
  ask `2 ∈ 3` or `Bool ∩ ℕ = ∅`.

* Proofs in type theory are constructive: GCD example. This is what we
  use to write functional programs.

We define a programming language by listing all the ways to construct
programs of different types and equalities which explain how programs
run.


# Simple type theory

## `Bool`

Rules:

* introduction:
  * `true : Bool`
  * `false : Bool`
* elimination:
  * if `t : Bool`, `u : A`, `v : A`, then `if t then u else v : A`
    * this works for any `A`
* computation:
  * `if true then u else v = u`
  * `if false then u else v = u`

Examples. How many terms of type `Bool` can you write with these
rules?

    b1 b2 b3 b4 : Bool
    b1 = true
    b2 = false
    b3 = if b1 then b2 else b1
    b4 = if b3 then b1 else b2

Let's compute:

`b3 = if b1 then b2 else b1 = if true then b2 else b1 = b2 = true`

## Funcion space: `A → B` (for any two types `A`, `B`)

Rules:

* introduction:
  * if `t : B` and `t` can contain `x` and `x : A`, then `(λ x → t) : (A → B)`
* elimination:
  * if `t : A → B` and `u : A`, then `t u : B`
* computation:
  * `(λ x → t) u = t[x↦u]` where `t[x↦u]` means that all copies of
    `x` are replaced by `u`
* uniqueness:
  * `(λ x → t x) = t`

Examples, compute!

    id id' id'' : Bool → Bool
    id = λ x → x
    id' = λ x → if x then true else false
    id'' = λ x → if true then x else false

Do we have `id = id'`? Do we have `id = id''`?

    not

    b5 : Bool
    b5 = id true

Multiple arguments, currying.

Notation: `A → B → C` means `A → (B → C)`, `λ x y → t` means `λ x → λ
y → t`, `t u v` means `(t u) v`.

    and
    or
    xor

## `ℕ`



## `A × B`

## `A ⊎ B`

## Propositional logic

Maybe talk about Curry-Howard?


# Indexed types

Vectors

Equality

Inductive types in general

## Predicate logic

Do some discrete math.

Internalise simple type theory. Define a model in which `id` is not
equal to `id'`?
