# Meta

You can take semi-compulsory courses in later semesters.

You have to register with the correct code:

 * BSc: IP-18KVSZTME
 * MSc: IPM-18sztKVTEE
 * MSc evening course: IPM-18EsztKVTEE

Teacher of lecture: Kaposi Ambrus ([website](http://akaposi.web.elte.hu))

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

    t : A

t is a term (program), A is its type

examples: `(1 + 1) : ℕ`, `(λ b → if b then 1 else 3) : Bool → ℕ`

Sometimes type theory means the study of type systems for programming
languages. Here we study Martin-Löf's type theory. This is a
functional programming language and a foundation of mathematics at the
same time.

It can be used as a replacement for set theory. Differences:

 * `x ∈ A` in set theory is a proposition, while `t : A` is a
   judgement (analogy: static and dynamic type systems: Haskell vs
   Python). In type theory, `1 + 1 = 2` is at a different level from
   `(1 + 1) : ℕ`, but in set theory `1 + 1 = 2` and `(1 + 1) ∈ ℕ` are
   both propositions. Representation independence in type theory, we
   cannot ask `2 ∈ 3` or `Bool ∩ ℕ = ∅`.

 * Proofs in type theory are constructive: GCD example. This is what
   we use to write functional programs.

We define a programming language by listing all the ways to construct
programs of different types and equalities which explain how programs
run.


# Simple type theory

Type theory is a game which we play with a finite number of rules. For
each type former, there is a number of rules. In this section, we
learn about the rules for `Bool`, `→`, `ℕ`, `×`, abstract types, `⊥`,
`⊤`, `⊎`. We also learn that equality of terms is decidable, the
difference between equality and behaviour, the algebraic structure of
types and the connection to propositional logic.

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

Examples.

    b1 b2 b3 b4 : Bool
    b1 = true
    b2 = false
    b3 = if b1 then b2 else b1
    b4 = if b3 then b1 else b2

Let's compute:

`b3 = if b1 then b2 else b1 = if true then b2 else b1 = b2 = false`

Question: how many terms of type `Bool` can you write with these
rules? Answer: only two, everything is equal to either `true` or
`false`.

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

Examples.

    id idy id1 id' id'' : Bool → Bool
    id = λ x → x
    idy = λ y → y
    id1 = λ x → id x
    id' = λ x → if x then true else false
    id'' = λ x → if true then x else false

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

We don't have `id = id'` but we do have `id = id''`.

More examples.

    not : Bool → Bool
    not = λ x → if x then false else true

    b5 : Bool
    b5 = id true

Question: how many elements of `Bool → Bool` are there? Answer:
infinitely many, e.g. `λ x → not x`, `λ x → not (not x)`, `λ x → not
(not (not x))`, `λ x → not (not (not (not x)))` etc.

Multiple arguments, currying.

Notation: `A → B → C` means `A → (B → C)`, `λ x y → t` means `λ x → λ
y → t`, `t u v` means `(t u) v`. `λ` extends as far right as possible,
so `λ x → t u = λ x → (t u)` instead of `(λ x → t) u`.

    and : Bool → Bool → Bool
    and = λ x y → if x then y else false

## Equality checking in Agda

It is possible to decide for any two terms whether they are
equal. Agda implements this as follows: it can normalise (`C-c C-n`)
any two terms, that is, unfold all the abbreviations and use the
computation and uniqueness rules to simplify them. Once the two terms
are normalised, if they coincide (up to renaming of bound variables),
they are equal. If they don't, they are not equal.

## Equality and behaviour

There are only 4 terms of type `Bool → Bool` if we only consider
behaviour, but there are infinitely many up to equality.

Question: if two terms have different behaviour, can they be still
equal? Answer: no.

Question: why are terms which have the same behaviour different? Can't
we make behaviour and equality coincide? Answer: for `Bool`, we could
do this by adding the rule

 * if `t[x↦true] = t'[x↦true]` and `t[x↦false] = t'[x↦false]` then `t = t'`.

But this wouldn't be very efficient. If we wanted to check two terms
`t`, `t'` each containing `n` `Bool`-variables, then we would need to
check `2ⁿ` cases when deciding `t = t'`.

If we added the same kind of rules for `ℕ` (see below), we would need
to check infinitely many equalities. Hence, equality checking for
terms would become undecidable.

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
    
    even : ℕ → Bool

Question: is there a function of type `ℕ → ℕ` which cannot be given by
primrec?

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

Question: how many terms of type `Bool × Bool` are there? Answer:
four.

Example.

    uncurry : (Bool → Bool → Bool) → Bool × Bool → Bool

Question: `A → B → C` represents `A × B → C`. Is there a way to
represent `A → B × C` without `×`? Answer: yes, using two separate
terms of types `A → B` and `A → C`, respectively.

Without the uniqueness rule, the following two terms of type `Bool ×
Bool → Bool × Bool` would be not equal:

    λ x → x

    λ x → (proj₁ x , proj₂ x)

## Abstract types

Rules: `X`, `Y`, `Z` are types. That's it.

Question: how many possible terms are of the following types?

                                             Answer:
    idX     : X → X                          1
    pick    : X → X → X                      2
    pick*   : X → (X → X) → X                ∞
    pick?   : (X → X) → X                    0
    
    swap    : X × Y → Y × X                  1

If we can write a function for abstract types, we can also write it
for concrete ones. E.g. `pick = λ x y → x : X → X → X`, but we can
write a `pickBool = λ x y → x : Bool → Bool → Bool`.

## Empty type: `⊥`

Rules:

 * elimination:
    * if `t : ⊥` then `exfalso t : C` for any type `C`

Example.

    magicZ : (X → ⊥) → X → Z

## Unit type: `⊤`

 * introduction:
    * `tt : ⊤`
 * uniqueness:
    * if `t : ⊤` then `t = tt`

Question: how many terms are there of the following types?

    interesting   : ⊥ → X
    uninteresting : X → ⊤

## Coproducts: `A ⊎ B`

Rules:

 * introduction:
    * if `u : A` then `inj₁ u : A ⊎ B`
    * if `v : B` then `inj₂ v : A ⊎ B`
 * elimination:
    * if `u : A → C`, `v : B → C` and `t : A ⊎ B` then `case t u v : C`
 * computation:
    * `case (inj₁ t) u v = u t`
    * `case (inj₂ t) u v = v t`

Example.

    undiag : X ⊎ X → X

## Logical equivalence `↔` and an algebraic structure on types

We have all finite types now:

    type       	    	 number of elements
    ⊤          	    	 1
    ⊤ ⊎ ⊤      	    	 2
    ⊤ ⊎ ⊤ ⊎ ⊤  	    	 3
    ⊤ ⊎ ⊤ ⊎ ⊤ ⊎ ⊤   	 4
    ...                  ...

For finite types, the type formers `⊎`, `×`, `→` work like addition,
multiplication and exponentiation for natural numbers. If we denote
the number of terms of type `A` by |`A`|, we have:

 * |`⊥`| = 0
 
 * |`⊤`| = 1

 * |`A ⊎ B`| = |`A`| + |`B`|
 
 * |`A × B`| = |`A`| * |`B`|

 * |`A → B`| ≥ |`B`| ^ |`A`| (here we can have more elements as we saw
   for `Bool → Bool`)

The mathematical operations obey some laws, e.g. associativity of
multiplication: $(x * y) * z = x * (y * z)$.  The same laws hold for
types, and not only for finite types, but for any type including
infinite ones like `ℕ`.

`A ↔ B` abbreviates `(A → B) × (B → A)` for any `A`, `B`, and we call
a `t : A ↔ B` a logical equivalence between `A` and `B`.

The law corresponding to associativity of multiplication given for
abstract types `X`, `Y`, `Z`:

    ass× : (X × Y) × Z ↔ X × (Y × Z)
    ass× = (λ w → (proj₁ (proj₁ w) , (proj₂ (proj₁ w) , proj₂ w)) , λ w → ((proj₁ w , proj₁ (proj₂ w)) , proj₂ (proj₂ w)))

We summarise the laws.

Types form a commutative monoid with `⊎`, `⊥`:

 * `(X ⊎ Y) ⊎ Z ↔ X ⊎ (Y ⊎ Z)` (associativity, $(x+y)+z = x+(y+z)$)

 * `X ⊎ ⊥ ↔ X` (unit element, $x+0 = x$)

 * `X ⊎ Y ↔ Y ⊎ X` (commutativity, $x+y = y+x$)

Types form a commutative monoid with a null element with `×`, `⊤`,
`⊥`:

 * `(X × Y) × Z ↔ X × (Y × Z)` ($(x * y) * z = x * (y * z)$)

 * `X × ⊤ ↔ X` ($x * 1 = x$)

 * `X × Y ↔ Y × X` ($x * y = y * x$)

 * `X × ⊥ ↔ ⊥` ($x * 0 = 0$)

We also have distributivity:

 * `(X ⊎ Y) × Z ↔ (X × Z) ⊎ (Y × Z)` ($(x+y) * z = (x * z) + (y*z)$)

These above are called a commutative semiring structure on types (semi
because addition has no inverse).

For exponentiation we have:

 * `(X ⊎ Y) → Z ↔ (X → Z) × (Y → Z)` ($z^{x+y} = (z^x)*(z^y)$)

 * `(X × Y) → Z ↔ X → (Y → Z)` ($z^{x*y} = ({z^y})^x$)

 * `⊥ → X ↔ ⊤` ($x^0=1$)

 * `⊤ → X ↔ X` ($x^1=x$)

 * `X → ⊤ ↔ ⊤` ($1^x=1$)

We say that `A` and `B` are isomorphic if there is a logical
equivalence `(u , v) : A ↔ B` such that `λ x → v (u x) = λ x → x` and
`λ y → u (v y) = λ y → y`. We denote this by `A ≅ B` (this is not a
type in Agda).

Example. `(X × Y) × Z ≅ X × (Y × Z)` by the above definition `(u , v)
= ass×`:

    λ x → v (u x) = 
                                                                    by definition of u
    λ x → v (proj₁ (proj₁ x) , (proj₂ (proj₁ x) , proj₂ x)) =
                                                                    by definition of v (we write _ for some long terms that won't matter)
    λ x → ((proj₁ (proj₁ (proj₁ x) , _) ,
            proj₁ (proj₂ (_ , (proj₂ (proj₁ x) , _)))) ,
           proj₂ (proj₂ (_ , (_ , proj₂ x)))) =
                                                                    by the computation rules for ×
    λ x → ((proj₁ (proj₁ x) ,
            proj₂ (proj₁ x)) ,
           proj₂ x) =
                                                                    by the uniqueness rule for ×
    λ x → (proj₁ x , proj₂ x)
                                                                    by the uniqueness rule for ×
    λ x → x

You can check that this is the case for the other direction. Also,
check the same in Agda!

## Negation `¬` and propositional logic

`t : A` in programming means that the program `t` has type `A`.

`t : A` in logic means `t` is a proof of `A`. You can think about a
type as a set of its proofs.

Negation: `¬ A` abbreviates `A → ⊥`.

Examples.

    return : X → ¬ ¬ X
    join   : ¬ ¬ ¬ ¬ X → ¬ ¬ X

Translation:

| type theory       | programming                               | logic                         |
|:-----------------:|:-----------------------------------------:|:-----------------------------:|
| `X`, `Y`, `Z`     | abstract types                            | propositional variables       |
| `A → B`           | function                                  | implication, `A ⊃ B`, `A ⇒ B` |    
| `A × B`           | record, multiple inputs                   | conjunction, `A ∧ B`    	|
| `⊤`               | unit, void (in C)                         | true         		  	|
| `⊥`               | empty type (uncommon)                     | false        		  	|
| `A ⊎ B`           | disjoint union, superclass of `A` and `B` | disjunction, `A ∨ B`    	|
| `¬ A`             | `A` has no elements (uncommon)            | negation, `¬ A`         	|
| `A ↔ B`           | functions in both direction               | if and only if, `⇔`     	|
|                   |                                           |                         	|
|                   |                                           |                         	|
|                   |                                           |                         	|
| `Bool`            | `Bool`                                    | (`𝟚`)       		  	|
| `ℕ`               | `unsigned int`                            | (`ℕ`)        		  	|

Some laws of logic (in addition to the semiring laws above), all up to
`↔`.

 * `¬ X ⊎ Y → (X → Y)`, but not the other direction.

 * De Morgan laws (one missing):

    * `¬ (X ⊎ Y) ↔ ¬ X × ¬ Y`
    
    * `¬ (X × Y) ← ¬ X ⊎ ¬ Y`

 * No contradiction: `¬ (X ↔ ¬ X)`

 * `¬¬` is involutive: `¬ ¬ ¬ ¬ X ↔ ¬ ¬ X`

 * Classical logic: `¬ ¬ (¬ ¬ X → X)`

TODO: universe, large functions which compute types.

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
