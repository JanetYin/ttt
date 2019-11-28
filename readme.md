# Meta

You can take semi-compulsory courses in later semesters.

You have to register with the correct code:

 * BSc: IP-18KVSZTME
 * MSc: IPM-18sztKVTEE
 * MSc evening course: IPM-18EsztKVTEE

Teacher of the lectures: Kaposi Ambrus
([website](http://akaposi.web.elte.hu))

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

Examples: `(1 + 1) : ℕ`, `(λ b → if b then 1 else 3) : Bool → ℕ`.

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

Type theory is a game that we play with a finite set of rules. For
each type former, there is a number of rules. In this section, we
learn the rules for type formers `Bool`, `→`, `ℕ`, `×`, abstract
types, `⊥`, `⊤`, `⊎`. We also learn that equality of terms is
decidable, the difference between equality and behaviour, the
algebraic structure of types and how to translate propositional logic
formulas to types.

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

But this wouldn't be very efficient. If we wanted to check if two
terms `t`, `t'` each containing `n` `Bool`-variables are equal, then
we would need to check `2ⁿ` cases.

If we added the same kind of rules for `ℕ` (see below), we would need
to check infinitely many equalities. Hence, equality checking for
terms would become undecidable.

We say that equality in type theory is *intensional*. In contrast, if
it was extensional, equality of functions would be determined by their
extensions: all the possible use cases.

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
    plus3 = λ x → suc (suc (suc x))

    even : ℕ → Bool
    even = λ x → primrec true (λ _ b → not b) x

    times3plus2 : ℕ → ℕ
    times3plus2 = λ x → primrec (suc (suc zero)) (λ _ n → suc (suc (suc n))) x

    plus : ℕ → ℕ → ℕ
    plus = λ x y → primrec y (λ _ n → suc n) x
    
    pred : ℕ → ℕ
    pred = λ x → prmirec zero (λ n _ → n) x

We write (even in Agda) `0` for `zero`, `1` for `suc zero`, `2` for
`suc (suc zero)`, and so on.

`primrec u v t` roughly replaces `zero` by `u` and `suc`s by
`v`s. More precisely, `v` also receives the number itself (which we
only used in the definition of `pred` above). The first few cases:

    x                                    primrec u v x
    -----------------------------------------------------------------
    0 = zero                             u
    1 = suc zero                         v 0 u
    2 = suc (suc zero)                   v 1 (v 0 u)
    3 = suc (suc (suc zero))             v 2 (v 1 (v 0 u))
    4 = suc (suc (suc (suc zero)))       v 3 (v 2 (v 1 (v 0 u)))
    ...                                  ...

A more complicated example: equality checking of two natural numbers.

    eq : ℕ → ℕ → Bool
    eq = λ x → primrec is0 (λ _ → f) x

This is how `eq` works:

    x                                    eq x
    -----------------------------------------------------------------
    0 = zero                             is0
    1 = suc zero                         is1 = f is0
    2 = suc (suc zero)                   is2 = f (f is0)
    3 = suc (suc (suc zero))             is3 = f (f (f is0))
    4 = suc (suc (suc (suc zero)))       is4 = f (f (f (f is0)))
    ...                                  ...

`is0` decides whether its input is `0`:

    is0 : ℕ → Bool
    is0 = λ y → primrec true (λ _ _ → false) y

If we look at the above table, we can see what `f` has to do: from a
function which decides whether a number is `n`, it has to create a
function which decides whether a number is `suc n`.

    f : (ℕ → Bool) → (ℕ → Bool)
    f = λ isn → λ y → primrec false (λ y' _ → isn y') y

If `y` is `zero`, it is certainly not `suc n` (hence the first
argument of `primrec` is `false`), if `y` is `suc y'`, then we know
that `suc n = suc y'` iff `n = y'`. And this can be decided by `isn`.

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

Rules:

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
because addition has no inverse). See also Tarski's high school
algebra.

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

Some types can be seen as logical propositions. There is a translation
from a proposition `P` to a type, we denote this by `⟦ P ⟧`. We also
write how programmers view the type that a logical connective is
translated to.

| logic                         | translation                       | programming                                       |
|:-----------------------------:|:---------------------------------:|:-------------------------------------------------:|
| propositional variables       | `⟦ V ⟧       := X`                | abstract type                                     |
| implication                   | `⟦ P ⇒ Q ⟧   := ⟦ P ⟧ → ⟦ Q ⟧`    | function                                          |    
| conjunction                   | `⟦ P ∧ Q ⟧   := ⟦ P ⟧ × ⟦ Q ⟧`    | record, multiple inputs                           |
| true                          | `⟦ True ⟧    := ⊤`                | unit (in C, C++, Java: void)                      |
| false                         | `⟦ False ⟧   := ⊥`                | empty type (uncommon)                             |
| disjunction                   | `⟦ P ∨ Q ⟧   := ⟦ P ⟧ ⊎ ⟦ Q ⟧`    | disjoint union, superclass of `⟦ P ⟧` and `⟦ Q ⟧` |
| negation                      | `⟦ ¬ P ⟧     := ⟦ P ⟧ → ⊥`        | `⟦ P ⟧` has no elements (uncommon)                |
| if and only if                | `⟦ P iff Q ⟧ := ⟦ P ⟧ ↔ ⟦ Q ⟧`    | functions in both direction                       |

Now `t : ⟦ P ⟧` can be read as `t` is a proof of the proposition
`P`.

Inspired by this, we introduce negation: `¬ A` abbreviates `A → ⊥`.

Examples.

    return : X → ¬ ¬ X
    join   : ¬ ¬ ¬ ¬ X → ¬ ¬ X

Some laws of logic (in addition to the semiring laws above).

 * `¬ X ⊎ Y → (X → Y)`, but not the other direction.

 * De Morgan laws (one missing):

    * `¬ (X ⊎ Y) ↔ ¬ X × ¬ Y`
    
    * `¬ (X × Y) ← ¬ X ⊎ ¬ Y`

 * No contradiction: `¬ (X ↔ ¬ X)`

 * `¬¬` is involutive: `¬ ¬ ¬ ¬ X ↔ ¬ ¬ X`

 * Classical logic: `¬ ¬ (¬ ¬ X → X)`

# Universes

We write the type of types as `Set`. For example, `Bool : Set`,
`ℕ ⊎ ⊤ : Set` etc.

We can write functions which create sets.

    _^2 : Set → Set
    _^2 = λ A → A × A

    _^_ : Set → ℕ → Set
    _^_ = λ A n → primrec ⊤ (λ _ As → A × As) n

For example, we have `Bool ^ 3 = Bool × (Bool × (Bool × ⊤))`.

    tff : Bool ^ 3
    tff = true , (false , (false , tt))

We have `Set : Set₁`, `Set₁ : Set₂`, and so on.

Two ways of defining equality on `Bool`:

    eqb : Bool → Bool → Bool
    eqb = λ x y → if x then y else not y

    Eqb : Bool → Bool → Set
    Eqb = λ x y → if x then (if y then ⊤ else ⊥) else (if y then ⊥ else ⊤)

 * For any two booleans `x` and `y`, `eqb x y` is another boolean,
   while `Eqb x y` is a type.

 * `Eqb x y` has an element if and only if `x` and `y` are the same booleans.

 * `Eqb x y` is the proposition saying that `x` is equal to `y`.

 * `x = y` is a metatheoretic statement saying that the terms `x` and
   `y` are the same. It is not a type in Agda.

Examples:

    true=true : Eqb true true
    true=true = tt

    notUnitTest : Eqb (not (not true)) true
    notUnitTest = tt

    ¬true=false : ¬ Eqb true false
    ¬true=false = λ e → e

Equality type for `ℕ`:

    Eqn : ℕ → ℕ → Set
    Eqn = λ x y → Eqb (eq x y) true

You can check that this has the following properties:

    Eqn zero    zero    = ⊤
    Eqn (suc x) zero    = ⊥
    Eqn zero    (suc y) = ⊥
    Eqn (suc x) (suc y) = Eqn x y

Unit tests for functions on natural numbers:

    test+ : Eqn (3 + 2) 5
    test+ = tt

We even have negative unit tests:

    test+' : ¬ Eqn (3 + 2) 4
    test+' = λ x → x

# Dependent types

## Dependent functions: `(x : A) → B`

Rules:

 * type formation:
    * if `A` is a type and `B` is a type assuming `x : A`, then
      `(x : A) → B` is a type
 * elimination:
    * if `t : (x : A) → B` and `u : A`, then `t u : B[x↦u]`
 * introduction:
    * if `t : B` assuming `x : A` then `(λ x → t) : (x : A) → B`
 * computation:
    * `(λ x → t) u = t[x↦u]`
 * uniqueness:
    * `(λ x → t x) = t`

Simply typed functions `A → B` are a special case of dependent
functions when `B` does not contain `x`.

We don't need abstract types anymore.

    id : (A : Set) → A → A
    id = λ A x → x

    comm× : (A B : Set) → (A × B) ↔ (B × A)
    comm× = λ A B → ((λ w → proj₂ w , proj₁ w) , (λ w → proj₂ w , proj₁ w))

Abbreviations: `(x : A)(y : B) → C` abbreviates `(x : A) → (y : B) → C`.
`(x y : A) → B` abbreviates `(x : A)(y : A) → B`.

## Dependent pairs: `Σ A B`

Rules:

 * type formation:
    * if `A` is a type and `B : A → Set`, then
      `Σ A B` is a type
 * introduction:
    * if `u : A` and `v : B u`, then `u , v : Σ A B`
 * elimination:
    * if `t : Σ A B` then `proj₁ t : A`
    * if `t : Σ A B` then `proj₂ t : B (proj₁ t)`
 * computation:
    * `proj₁ (u , v) = u`
    * `proj₂ (u , v) = v`
 * uniqueness:
    * `(λ x → t x) = t`

`A × B` can be defined as `Σ A (λ _ → B)`.

Example:

    w : Σ ℕ (λ n → Eqn (suc zero + n) (suc (suc (suc zero))))
    w = (suc (suc zero) , tt)

## Dependent elimination for `Bool`, `ℕ` and `⊎`

Rules:

 * elimination:
    * `indℕ    : (P : ℕ     → Set) → P zero → ((n : ℕ) → P n → P (suc n)) → (t : ℕ) → P t`
    * `indBool : (P : Bool  → Set) → P true → P false → (t : Bool) → P t`
    * `ind⊎    : (P : A ⊎ B → Set) → ((a : A) → P (inj₁ a)) → ((b : B) → P (inj₂ b)) → (t : A ⊎ B) → P t`
 * computation:
    * `indℕ P u v zero = u`
    * `indℕ P u v (suc t) = v t (indℕ P u v t)`
    * `indBool P u v true  = u`
    * `indBool P u v false = v`
    * `ind⊎ P u v (inj₁ t) = u t`
    * `ind⊎ P u v (inj₂ t) = v t`

`primrec`, `if_then_else`, `case` can be defined using `indℕ`,
`indBool`, `ind⊎`, respectively.

Examples:

    ⊤s : (n : ℕ) → ⊤ ^ n
    ⊤s = indℕ (λ n → ⊤ ^ n) tt (λ n tts → tt , tts)

    notInvolutive : (x : Bool) → Eqb (not (not x)) x
    notInvolutive = λ x → indBool (λ x → Eqb (not (not x)) x) tt tt x

We want to prove `Eqb (not (not x)) x` for every `x : Bool`. We do
this by induction, that is, for every constructor for `Bool` (`x =
true` and `x = false`) we have to show `Eqb (not (not x)) x`. In the
first case we need `Eqb (not (not true)) true = Eqb true true = ⊤`, in
the second case we need `Eqb (not (not false)) false = Eqb false false
= ⊤`. So we prove both cases simply be `tt`.

We show that `zero` is a left and right identity of addition.

    plusLeftId : (x : ℕ) → Eqn (plus zero x) x
    plusLeftId = λ x → indℕ (λ x → Eqn x x) tt (λ _ e → e) x

First we note that `Eqn (plus zero x) x = Eqn x x`. So we only have to
prove `Eqn x x` for every `x : ℕ`. Induction says that we have to
prove this first for `x = zero`, that is `Eqn zero zero = ⊤`, this is
easy: `tt`. Then, for any `n : ℕ`, given `e : Eqn n n`, we have to
show `Eqn (suc n) (suc n)`. `e` is called the inductive
hypothesis. But as we remarked above, `Eqn (suc n) (suc n) = Eqn n n`,
so we can direcly reuse the induction hypothesis to prove the case for
`x = suc n`.

## Predicate logic

Universal and existential quantifiers can also be translated to types:

| logic                         | translation                            |
|:-----------------------------:|:--------------------------------------:|
| implication                   | `⟦ P ⇒ Q ⟧   	 := ⟦ P ⟧ → ⟦ Q ⟧`     	 |
| conjunction                   | `⟦ P ∧ Q ⟧   	 := ⟦ P ⟧ × ⟦ Q ⟧`     	 |
| true                          | `⟦ True ⟧    	 := ⊤`                 	 |
| false                         | `⟦ False ⟧   	 := ⊥`                 	 |
| disjunction                   | `⟦ P ∨ Q ⟧   	 := ⟦ P ⟧ ⊎ ⟦ Q ⟧`     	 |
| negation                      | `⟦ ¬ P ⟧     	 := ⟦ P ⟧ → ⊥`         	 |
| if and only if                | `⟦ P iff Q ⟧ 	 := ⟦ P ⟧ ↔ ⟦ Q ⟧`     	 |
| forall                        | `⟦ ∀x∈ℕ, P x ⟧ := (x : ℕ) → ⟦ P x ⟧` 	 |
| exists                        | `⟦ ∃x∈ℕ, P x ⟧ := (Σ ℕ λ x → ⟦ P x ⟧)` |

Prove the following theorems (easy):

       (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
       (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a ⊎ Q a)  ← ((a : A) → P a) ⊎ ((a : A) → Q a)
       (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a × Q a)  → Σ A P × Σ A Q
       (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a)  ↔ Σ A P ⊎ Σ A Q
       (A : Set)(P : A → Set)              → (Σ A λ a → ¬ P a)      → ¬ ((a : A) → P a)
       (A : Set)(P : A → Set)              → (¬ Σ A λ a → P a)      ↔ ((a : A) → ¬ P a)
       (A B : Set)                         → (A ⊎ B)                ↔ Σ Bool (λ b → if b then A else B)

We can also prove the following theorems.

    ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (((a : A) → P a ⊎ Q a) → ((a : A) → P a) ⊎ ((a : A) → Q a)))
    ¬ ((A : Set)(P : A → Set)(Q : A → Set) → ((Σ A λ a → P a × Q a) ← Σ A P × Σ A Q))

These are negated theorems, so we need to construct functions where
the input has a huge type and the output is `⊥`. We have to come up
with counterexamples. E.g. the first one says that for all sets and
two predicates on the set, if for all elements of the set, one of the
predicates holds, then one of the predicates holds for all
elements. Here is a counterexample:

    A = ℕ
    P = isEven
    Q = isOdd

So, the proof is

    λ f → case (f ℕ isEven isOdd everyℕisEvenOrOdd) (λ allEven → allEven (suc zero)) (λ allOdd → allOdd zero)

where `everyℕisEvenOrOdd` is a proof that `(a : ℕ) → isEven a ⊎ isOdd
a`.

## Properties of `ℕ` and pattern matching

Addition:

    _+_ : ℕ → ℕ → ℕ
    _+_ = λ x y → primrec y (λ _ n → suc n) x

A shorter notation for this in Agda:

    x + y = primrec y (λ _ n → suc n) x

Pattern matching definition:

    zero  + y = y
    suc x + y = suc (x + y)

Note that this contains the same amount of information as the
`primrec` variant and its behaviour is the same. Similarly, equality
of natural numbers can be redefined this way:

    eq : ℕ → ℕ → Bool
    eq zero    zero    = true
    eq (suc x) zero    = false
    eq zero    (suc y) = false
    eq (suc x) (suc y) = eq x y

    toSet : Bool → Set
    toSet true  = ⊤
    toSet false = ⊥

    Eqn : ℕ → ℕ → Set
    Eqn x y = toSet (eq x y)

Every such pattern matching definition can be rewritten into a
definition using `primrec` or `indℕ`. Hardcore people only use the
eliminators, lazy people use pattern matching.

Properties of this equality:

    refl : (x : ℕ) → Eqn x x
    refl zero = tt
    refl (suc x) = refl x

    transport : (P : ℕ → Set)(x y : ℕ) → Eqn x y → P x → P y
    transport P zero    zero    e u = u
    transport P (suc x) zero    e u = exfalso e
    transport P zero    (suc y) e u = exfalso e
    transport P (suc x) (suc y) e u = transport (λ x → P (suc x)) x y e u

    sym : (x y : ℕ) → Eqn x y → Eqn y x
    sym x y e = transport (λ z → Eqn z x) x y e (refln x)

    trans : (x y z : ℕ) → Eqn x y → Eqn y z → Eqn x z
    trans x y z e e' = transport (λ q → Eqn x q) y z e' e

    cong : (f : ℕ → ℕ)(x y : ℕ) → Eqn x y → Eqn (f x) (f y)
    cong f x y e = transport (λ y → Eqn (f x) (f y)) x y e (refln (f x))
    
`zero` and `suc` are disjoint and successor is injective:

    zero≠suc : (x : ℕ) → ¬ Eqn zero (suc x)
    zero≠suc x e = e

    suc-inj : (x y : ℕ) → Eqn (suc x) (suc y) → Eqn x y
    suc-inj x y e = e

Natural numbers form a commutative monoid with `_+_` and `zero`.

    idl : (x : ℕ) → Eqn (zero + x) x
    idl x = refln x

    idr : (x : ℕ) → Eqn (x + zero) x
    idr zero    = tt
    idr (suc x) = idr x

    ass : (x y z : ℕ) → Eqn ((x + y) + z) (x + (y + z))
    ass zero    y z = refln (y + z)
    ass (suc x) y z = ass x y z

    comm-lemm : (x y : ℕ) → Eqn (suc x + y) (x + suc y)
    comm-lemm zero    y = refln y
    comm-lemm (suc x) y = comm-lemm x y

    comm : (x y : ℕ) → Eqn (x + y) (y + x)
    comm zero y    = sym (y + zero) y (idr y)
    comm (suc x) y = trans (suc (x + y)) (suc (y + x)) (y + suc x) (comm x y) (comm-lemm y x)

Prove `Eqn ((x + y) ^ 2) (x ^ 2 + 2 * x * y + y ^ 2)` using the
algebraic laws, `cong` and `trans`.

In the tutorials, show that natural numbers form a commutative
semiring with `+` and `*`. You can follow the [discrete math
textbook](https://bitbucket.org/akaposi/ttt/src/master/muveletek_termeszetes_szamokkal.pdf).

Less or equal.

    _≤_ : ℕ → ℕ → Set
    zero  ≤ y     = ⊤
    suc x ≤ zero  = ⊥
    suc x ≤ suc y = x ≤ y

    ex : 3 ≤ 100
    ex = tt
    
    refl≤ : (x : ℕ) → x ≤ x
    refl≤ zero = tt
    refl≤ (suc x) = refl≤ x

    trans≤ : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
    trans≤ zero    y       z       e e' = tt
    trans≤ (suc x) (suc y) (suc z) e e' = trans≤ x y z e e'

    ≤dec : (x y : ℕ) → x ≤ y ⊎ y ≤ x
    ≤dec zero y = inj₁ tt
    ≤dec (suc x) zero = inj₂ tt
    ≤dec (suc x) (suc y) = ≤dec x y

## Functions on vectors

    _^_ : Set → ℕ → Set
    A ^ zero  = ⊤
    A ^ suc x = A × A ^ x

`nil`, `cons`, `head`, `tail`

WE REACHED THIS POINT AT THE LECTURE.

    insert : ℕ → (l : ℕ) → ℕ ^ l → ℕ ^ (suc l)
    insert x zero    xs       = x , tt
    insert x (suc l) (y , xs) = case (≤dec x y)
      (λ _ → x , y , xs)
      (λ _ → y , insert x l xs)

    _∧_ : Bool → Bool → Bool
    true  ∧ true = true
    _     ∧ _    = false

    eq^ : (l : ℕ) → ℕ ^ l → ℕ ^ l → Bool
    eq^ zero xs ys = true
    eq^ (suc l) (x , xs) (y , ys) = eq x y ∧ eq^ l xs ys

    Eq^ : (l : ℕ) → ℕ ^ l → ℕ ^ l → Set
    Eq^ l xs ys = toSet (eq^ l xs ys)

    test : Eq^ 5 (insert 3 4 (1 , 2 , 4 , 5 , tt)) (1 , 2 , 3 , 4 , 5 , tt)
    test = tt

    sort : (l : ℕ) → ℕ ^ l → ℕ ^ l
    sort zero _ = tt
    sort (suc l) (x , xs) = insert x l (sort l xs)

## Isomorphisms internally

    (Bool → ℕ) ≅ ℕ × ℕ
