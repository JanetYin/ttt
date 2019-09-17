# Meta

You can take semi-compulsory courses in later semesters.

You have to register with the correct code:

* BSc: IP-18KVSZTME
* MSc: IPM-18sztKVTEE
* MSc evening course: IPM-18EsztKVTEE

Tutorials:

1. Kaposi Ágoston (Kedd 16:00-17:30 Déli Tömb 2-709 (PC 9))
2. Kovács András (Szerda 17:45-19:15 Északi Tömb 2.63 (PC 8))
3. Rafaël Bocquet (English, Csütörtök 19:30-21:00 Déli Tömb 00-410 (PC 1))

Requirements:

* Canvas quiz for each lecture
* At the beginning of each tutorial a small assignment in the bead
  system. Weekly homeworks in the same system help preparing.
* Exam on the computer during the exam period.

For the tutorial, you get the following marks according to how many
assignments you completed (out of 10, for each assignment you can get
0 or 1 points): 5-6: 2, 7: 3, 8: 4, 9-10: 5.

To enter the exam, you need 50% in Canvas quizes and a minimum 2 mark
for the tutorial.

Recommended literature:

* [Thorsten Altenkirch. Naive Type Theory](http://www.cs.nott.ac.uk/~psztxa/publ/fomus19.pdf)
* [Homotopy Type Theory book](http://saunders.phil.cmu.edu/book/hott-online.pdf) (especially Chapter 1 Type theory)
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

## Booleans: `Bool`

Rules:

 * introduction:
    * `true : Bool`
    * `false : Bool`
 * elimination:
    * if `t : Bool`, `u : A`, `v : A`, then `if t then u else v : A`
       * this works for any `A`
 * computation:
    * `if true then u else v = u`
    * `if false then u else v = v`

Examples. How many terms of type `Bool` can you write with these
rules?

    b1 b2 b3 b4 : Bool
    b1 = true
    b2 = false
    b3 = if b1 then b2 else b1
    b4 = if b3 then b1 else b2

Let's compute:

`b3 = if b1 then b2 else b1 = if true then b2 else b1 = b2 = true`

There are only two elements of `Bool`.

## Functions: `A → B` (for any two types `A`, `B`)

Rules:

 * elimination:
    * if `t : A → B` and `u : A`, then `t u : B`
 * introduction:
    * if `t : B` assuming `x : A` then `(λ x → t) : (A → B)`
       * `x` is just a name (a variable), it is not an arbitrary term
 * computation:
    * `(λ x → t) u = t[x↦u]` where `t[x↦u]` means that all copies of
      `x` are replaced by `u`
 * uniqueness:
    * `(λ x → t x) = t`

Examples, compute.

    id idy id1 id' id'' : Bool → Bool
    id = λ x → x
    idy = λ y → y
    id1 = λ x → id x
    id' = λ x → if x then true else false
    id'' = λ x → if true then x else false

Do we have `id = id'`? Do we have `id = id''`?

We have

    id =
                           by definition
    λ x → x =
                           by the computation rule for functions (x:=y, t:=y, u:=x)
    λ x → (λ y → y) x =
                           by the uniqueness rule for functions (x:=x, t:=(λ y → y))
    λ y → y =
                           by definition
    idy

How many elements of `Bool → Bool` are there? Infinitely many.

More examples.

    not

    b5 : Bool
    b5 = id true

Multiple arguments, currying.

Notation: `A → B → C` means `A → (B → C)`, `λ x y → t` means `λ x → λ
y → t`, `t u v` means `(t u) v`. `λ` extends as far right as possible,
so `λ x → t u = λ x → (t u)` instead of `(λ x → t) u`.

    and
    or
    xor

## Equality checking in Agda

It is possible to decide for any two terms whether they are
equal. Agda implements this as follows: it can normalise (`C-c C-n`)
any two terms, that is, unfold all the abbreviations and use the
computation and uniqueness rules to simplify them. Once two terms are
normalised, if they coincide (up to renaming of bound variables), they
are equal. If they don't, they are not equal.

## Equality and behaviour

There are only 4 terms of type `Bool → Bool` if we only consider
behaviour, but there are infinitely many up to equality. If two terms
have different behaviour, can they be still equal?

Why are they different? Can't we make these two things coincide?

## Natural numbers: `ℕ`

Rules:

 * introduction:
    * `zero : ℕ`
    * if `t : ℕ` then `suc t : ℕ`
 * elimination:
    * if `u : A`, `v : ℕ → A → A` and `t : ℕ` then `primrec u v t : A`
 * computation:
    * `primrec u v zero = u`
    * `primrec u v (suc t) = v t (primrec u v t)`

Examples.

    three : ℕ
    three = suc (suc (suc zero))

    plus3 : ℕ → ℕ

    times3plus2 : ℕ → ℕ

    plus : ℕ → ℕ → ℕ
    
    pred : ℕ → ℕ
    even : ℕ → Bool
    odd  : ℕ → Bool
    _*_ : ℕ → ℕ → ℕ
    _^_ : ℕ → ℕ → ℕ
    equal? : ℕ → ℕ → Bool
    _≥?_ : ℕ → ℕ → Bool

## Products: `A × B` (for any two types `A`, `B`)

Rules:

 * introduction:
    * if `u : A` and `v : B`, then `(u , v) : A × B`
 * elimination:
    * if `t : A × B` then `proj₁ t : A` and `proj₂ t : B`
 * computation:
    * `proj₁ (u , v) = u`
    * `proj₂ (u , v) = v`
 * uniqueness:
    * `(proj₁ t , proj₂ t) = t`

How many terms of type `Bool × Bool` are there?

## Abstract types

Rules: `A`, `B`, `C` are types. That's it.

Examples. How many possible definitions are there?

    idA     : A → A
    pick₁   : A → A → A
    pick₂   : A → A → A
    pick*   : A → (A → A) → A
    pick?   : (A → A) → A
    
    curry   : (A × B → C) → (A → B → C)
    uncurry : (A → B → C) → (A × B → C)
    swap    : A × B → B × A
    assoc   : (A × B) × C → A × (B × C)
    diag    : A → A × A

## Empty type

## Unit type

## Abbreviated types

`↔` and `¬`

## Coproducts: `A ⊎ B`

Rules:

 * introduction:
    * if `u : A` then `inj₁ u : A ⊎ B`
    * if `v : B` then `inj₂ v : A ⊎ B`
 * elimination:
    * if `u : A → C`, `v : B → C` and `t : A ⊎ B` then `case t u v : C`
 * computation:
    * `case u v (inj₁ t) = u t`
    * `case u v (inj₂ t) = v t`

## Propositional logic

Maybe talk about Curry-Howard?

Holes?

# Indexed types

Vectors

Equality

Disjointness of constructors of inductive types, injectivity of
constructors, pattern matching.

Inductive types in general

## Predicate logic

Do some discrete math.

Internalise simple type theory. Define a model in which `id` is not
equal to `id'`? Notion of simply typed CwF with extra structure or a
simplification of that? Canonicity?
