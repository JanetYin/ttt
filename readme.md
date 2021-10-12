# Meta

You can take semi-compulsory courses in later semesters.

You have to register with the correct code:

 * BSc: IP-18KVSZTME
 * MSc: IPM-18sztKVTEE
 * MSc evening course: IPM-18EsztKVTEE

Teacher of the lectures: Kaposi Ambrus (akaposi kukac inf.elte.hu).

Tutorial teachers: Batta Zsolt (afhbj7 kukac inf.elte.hu), Lezsák Domonkos (lijjo8 kukac inf.elte.hu), Végh Tamás (vetuaat kukac inf.elte.hu).

Lectures and tutorials will be partly in Microsoft Teams, in the group [Típuselmélet 2021 ősz (IPM-18sztKVTE, P-18KVSZTM, IPM-18EsztKVTE)](https://teams.microsoft.com/l/team/19%3aNbccBrW8Os0asNOlMxx-IB27LNxT3EqjeU33KRcywLg1%40thread.tacv2/conversations?groupId=086976ce-4e7b-42e2-a7a5-4c0c3645f472&tenantId=0133bb48-f790-4560-a64d-ac46a472fbbc). If you are not a member, ask one of the teachers to add you.

Language: Hungarian (English available upon request).

Requirements:

 * Canvas quiz for each lecture
 * At the beginning of each tutorial a small Agda assignment. Weekly homeworks help preparation.
 * Exam on the computer during the exam period. [Example exam](https://bitbucket.org/akaposi/ttt/raw/master/exampleExam.agda)

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

Examples: `(1 + 1) : ℕ`, `(λ b → if b then 1 else 3) : 𝟚 → ℕ`.

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
   cannot ask `2 ∈ 3` or `𝟚 ∩ ℕ = ∅`.

 * Proofs in type theory are constructive: GCD example. This is what
   we use to write functional programs.

We define a programming language by listing all the ways to construct
programs of different types and equalities which explain how programs
run.


# Simple type theory

Type theory is a game that we play with a finite set of rules. For
each type former, there is a number of rules. In this section, we
learn the rules for type formers `𝟚`, `→`, `ℕ`, `×`, `⊥`, `⊤`, `⊎`. We
also learn that equality of terms is decidable, the difference between
equality and behaviour, the algebraic structure of types and how to
translate propositional logic formulas to types.

## Booleans: `𝟚`

Rules:

 * introduction:
    * `tt : 𝟚`
    * `ff : 𝟚`
 * elimination:
    * if `t : 𝟚`, `u : A`, `v : A`, then `if t then u else v : A`
       * this works for any `A`
 * computation:
    * `if tt then u else v = u`
    * `if ff then u else v = v`

Examples.

    b1 b2 b3 b4 : 𝟚
    b1 = tt
    b2 = ff
    b3 = if b1 then b2 else b1
    b4 = if b3 then b1 else b2

Let's compute:

`b3 = if b1 then b2 else b1 = if tt then b2 else b1 = b2 = ff`

Question: how many terms of type `𝟚` can you write with these
rules? Answer: only two, everything is equal to either `tt` or
`ff`.

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

    id idy id1 id' id'' : 𝟚 → 𝟚
    id = λ x → x
    idy = λ y → y
    id1 = λ x → id x
    id' = λ x → if x then tt else ff
    id'' = λ x → if tt then x else ff

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

    not : 𝟚 → 𝟚
    not = λ x → if x then ff else tt

    b5 : 𝟚
    b5 = id tt

Question: how many elements of `𝟚 → 𝟚` are there? Answer:
infinitely many, e.g. `λ x → not x`, `λ x → not (not x)`, `λ x → not
(not (not x))`, `λ x → not (not (not (not x)))` etc.

Multiple arguments, currying.

Notation: `A → B → C` means `A → (B → C)`, `λ x y → t` means `λ x → λ
y → t`, `t u v` means `(t u) v`. `λ` extends as far right as possible,
so `λ x → t u = λ x → (t u)` instead of `(λ x → t) u`.

    and : 𝟚 → 𝟚 → 𝟚
    and = λ x y → if x then y else ff

## Equality checking in Agda

It is possible to decide for any two terms whether they are
equal. Agda implements this as follows: it can normalise (`C-c C-n`)
any two terms, that is, unfold all the abbreviations and use the
computation and uniqueness rules to simplify them. Once the two terms
are normalised, if they coincide (up to renaming of bound variables),
they are equal. If they don't, they are not equal.

## Equality and behaviour

There are only 4 terms of type `𝟚 → 𝟚` if we only consider
behaviour, but there are infinitely many up to equality.

Question: if two terms have different behaviour, can they be still
equal? Answer: no.

Question: why are terms which have the same behaviour different? Can't
we make behaviour and equality coincide? Answer: for `𝟚`, we could
do this by adding the rule

 * if `t[x↦tt] = t'[x↦tt]` and `t[x↦ff] = t'[x↦ff]` then `t = t'`.

But this wouldn't be very efficient. If we wanted to check if two
terms `t`, `t'` each containing `n` `𝟚`-variables are equal, then
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
    * if `u : A`, `v : A → A` and `t : ℕ` then `rec u v t : A`
 * computation:
    * `rec u v zero = u`
    * `rec u v (suc t) = v (rec u v t)`

Examples.

    three : ℕ
    three = suc (suc (suc zero))

    plus3 : ℕ → ℕ
    plus3 = λ x → suc (suc (suc x))

    eq0 : ℕ → 𝟚
    eq0 = λ y → rec tt (λ _ → ff) y

    even : ℕ → 𝟚
    even = λ x → rec tt (λ _ b → not b) x

    times3plus2 : ℕ → ℕ
    times3plus2 = λ x → rec 2 (λ n → suc (suc (suc n))) x

    plus : ℕ → ℕ → ℕ
    plus = λ x y → rec y (λ n → suc n) x

We write (even in Agda) `0` for `zero`, `1` for `suc zero`, `2` for
`suc (suc zero)`, and so on.

`rec u v t` replaces `zero` by `u` and `suc`s by
`v`s. The first few cases:

    x                                    rec u v x
    -----------------------------------------------------------------------------------------------
    0 = zero                             u
    1 = suc zero                         v u
    2 = suc (suc zero)                   v (v u)
    3 = suc (suc (suc zero))             v (v (v u))
    4 = suc (suc (suc (suc zero)))       v (v (v (v u)))
    ...                                  ...

Example `times3plus2`:

    x                                    times3plus2 x
    -----------------------------------------------------------------------------------------------
    0 = zero                             2
    1 = suc zero                         suc (suc (suc 2))
    2 = suc (suc zero)                   suc (suc (suc (suc (suc (suc 2)))))
    3 = suc (suc (suc zero))             suc (suc (suc (suc (suc (suc (suc (suc (suc 2))))))))
    ...                                  ...

Example `eq0`:

    x                                    eq0 x
    -----------------------------------------------------------------------------------------------
    0 = zero                             tt
    1 = suc zero                         (λ _ → ff) tt = ff
    2 = suc (suc zero)                   (λ _ → ff) ((λ _ → ff) tt) = ff
    3 = suc (suc (suc zero))             (λ _ → ff) ((λ _ → ff) ((λ _ → ff) tt)) = ff
    ...                                  ...

Question: how is this addition function different from the previous one?

    plus' = λ x y → rec x (λ n → suc n) y


## Products: `A × B` (for any two types `A`, `B`)

Rules:

 * introduction:
    * if `u : A` and `v : B`, then `(u , v) : A × B`
 * elimination:
    * if `t : A × B` then `π₁ t : A` and `π₂ t : B`
 * computation:
    * `π₁ (u , v) = u`
    * `π₂ (u , v) = v`
 * uniqueness:
    * `(π₁ t , π₂ t) = t`

Question: how many terms of type `𝟚 × 𝟚` are there? Answer:
four.

Example.

    uncurry : (𝟚 → ℕ → 𝟚) → 𝟚 × ℕ → 𝟚

Question: `A → B → C` represents `A × B → C`. Is there a way to
represent `A → B × C` without `×`? Answer: yes, using two separate
terms of types `A → B` and `A → C`, respectively.

Without the uniqueness rule, the following two terms of type `𝟚 ×
𝟚 → 𝟚 × 𝟚` would be not equal:

    λ x → x

    λ x → (π₁ x , π₂ x)

With the help of products, we can define more interesting `ℕ → ℕ`
functions.

    fib : ℕ → ℕ
    fib = λ x → π₂ (rec (0 , 1) (λ w → (π₂ w , π₁ w + π₂ w)) n)

    n                                    rec (0 , 1) (λ w → (π₂ w , π₁ w + π₂ w)) n
    ----------------------------------------------------------------------------------------
    0 = zero                             (0 , 1)
    1 = suc zero                         (1 , 1)
    2 = suc (suc zero)                   (1 , 2)
    3 = suc (suc (suc zero))             (2 , 3)
    4 = suc (suc (suc (suc zero)))       (3 , 5)
    ...                                  ...


## Empty type: `⊥`

Rules:

 * elimination:
    * if `t : ⊥` then `exfalso t : C` for any type `C`


## Unit type: `⊤`

Rules:

 * introduction:
    * `triv : ⊤`
 * uniqueness:
    * if `t : ⊤` then `t = triv`


## Coproducts: `A ⊎ B`

Rules:

 * introduction:
    * if `u : A` then `ι₁ u : A ⊎ B`
    * if `v : B` then `ι₂ v : A ⊎ B
 * elimination:
    * if `u : A → C`, `v : B → C` and `t : A ⊎ B` then `case t u v : C`
 * computation:
    * `case (ι₁ t) u v = u t`
    * `case (ι₂ t) u v = v t`

The predecessor function `pred : ℕ → ℕ ⊎ ⊤`:

    n                                    pred n
    ----------------------------------------------------------------
    0 = zero                             ι₂ triv
    1 = suc zero                         ι₁ zero
    2 = suc (suc zero)                   ι₁ (suc zero)
    3 = suc (suc (suc zero))             ι₁ (suc (suc zero))
    4 = suc (suc (suc (suc zero)))       ι₁ (suc (suc (suc zero)))
    ...                                  ...

    pred = λ n → rec (ι₂ triv) (λ w → case w (λ n → ι₁ (suc n)) (λ _ → ι₁ zero)) n

Equality of natural numbers `eqℕ : ℕ → ℕ → 𝟚`

    n                                    eqℕ n
    -------------------------------------------------
    0 = zero                             eq0
    1 = suc zero                         "eq0 ∘ pred"
    2 = suc (suc zero)                   "eq1 ∘ pred"
    3 = suc (suc (suc zero))             "eq2 ∘ pred"
    4 = suc (suc (suc (suc zero)))       "eq3 ∘ pred"
    ...                                  ...

Because `pred` returns a `ℕ ⊎ ⊤`, we have to handle the `ι₂ triv` case:

    n                                    eqℕ n
    --------------------------------------------------------------------------
    0 = zero                             eq0
    1 = suc zero                         λ m → case (pred m) eq0 (λ _ → ff)
    2 = suc (suc zero)                   λ m → case (pred m) eq1 (λ _ → ff)
    3 = suc (suc (suc zero))             λ m → case (pred m) eq2 (λ _ → ff)
    4 = suc (suc (suc (suc zero)))       λ m → case (pred m) eq3 (λ _ → ff)
    ...                                  ...
    
    eqℕ = λ n → rec eq0 (λ eqn m → case (pred m) eqn (λ _ → ff)) n


## Assumptions of types

Using `{X Y : Set} → `, we assume that `X` and `Y` are arbitrary
types. The term needs to work for any types `X` and `Y`.

Question: how many possible terms are of the following types?

                                                         Answer:
    idX     : {X : Set} → X → X                          1
    pick    : {X : Set} → X → X → X                      2
    pick*   : {X : Set} → X → (X → X) → X                ∞
    pick?   : {X : Set} → (X → X) → X                    0
    
    swap    : {X : Set} → X × Y → Y × X                  1

Agda can figure out concrete use cases. E.g.:

    id𝟚 : 𝟚 → 𝟚
    id𝟚 = idX

Question: how many terms are there of the following types?

    interesting   : {X : Set} → ⊥ → X
    uninteresting : {X : Set} → X → ⊤

Examples.

    magicZ : {X : Set} → (X → ⊥) → X → Z
    undiag : {X : Set} → X ⊎ X → X


## Logical equivalence `↔` and an algebraic structure on types

We have all finite types now:

    type       	    	 number of elements
    ⊥                    0
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
   for `𝟚 → 𝟚`)

The mathematical operations obey some laws, e.g. associativity of
multiplication: $(x * y) * z = x * (y * z)$.  The same laws hold for
types, and not only for finite types, but for any type including
infinite ones like `ℕ`.

`A ↔ B` abbreviates `(A → B) × (B → A)` for any `A`, `B`, and we call
a `t : A ↔ B` a logical equivalence between `A` and `B`.

The law corresponding to associativity of multiplication given for
abstract types `X`, `Y`, `Z`:

    ass× : (X × Y) × Z ↔ X × (Y × Z)
    ass× = (λ w → (π₁ (π₁ w) , (π₂ (π₁ w) , π₂ w)) , λ w → ((π₁ w , π₁ (π₂ w)) , π₂ (π₂ w)))

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
    λ x → v (π₁ (π₁ x) , (π₂ (π₁ x) , π₂ x)) =
                                                                    by definition of v (we write _ for some long terms that won't matter)
    λ x → ((π₁ (π₁ (π₁ x) , _) ,
            π₁ (π₂ (_ , (π₂ (π₁ x) , _)))) ,
           π₂ (π₂ (_ , (_ , π₂ x)))) =
                                                                    by the computation rules for ×
    λ x → ((π₁ (π₁ x) ,
            π₂ (π₁ x)) ,
           π₂ x) =
                                                                    by the uniqueness rule for ×
    λ x → (π₁ x , π₂ x)
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

**** ITT TARTUNK ****

# Universes

We write the type of types as `Set`. For example, `𝟚 : Set`,
`ℕ ⊎ ⊤ : Set` etc.

We can write functions which create sets.

    _^2 : Set → Set
    _^2 = λ A → A × A

    _^_ : Set → ℕ → Set
    _^_ = λ A n → rec ⊤ (λ As → A × As) n

For example, we have `𝟚 ^ 3 = 𝟚 × (𝟚 × (𝟚 × ⊤))`.

    tff : 𝟚 ^ 3
    tff = tt , (ff , (ff , tt))

We have `Set : Set₁`, `Set₁ : Set₂`, and so on.

Two ways of defining equality on `𝟚`:

    eqb : 𝟚 → 𝟚 → 𝟚
    eqb = λ x y → if x then y else not y

    Eqb : 𝟚 → 𝟚 → Set
    Eqb = λ x y → if x then (if y then ⊤ else ⊥) else (if y then ⊥ else ⊤)

 * For any two booleans `x` and `y`, `eqb x y` is another boolean,
   while `Eqb x y` is a type.

 * `Eqb x y` has an element if and only if `x` and `y` are the same booleans.

 * `Eqb x y` is the proposition saying that `x` is equal to `y`.

 * `x = y` is a metatheoretic statement saying that the terms `x` and
   `y` are the same. It is not a type in Agda.

Examples:

    tt=tt : Eqb tt tt
    tt=tt = tt

    notUnitTest : Eqb (not (not tt)) tt
    notUnitTest = tt

    ¬tt=ff : ¬ Eqb tt ff
    ¬tt=ff = λ e → e

Equality of natural numbers:

    eqℕ : ℕ → ℕ → 𝟚 -- see above
    
    Eqℕ : ℕ → ℕ → Set
    Eqℕ a b = if eqℕ a b then ⊤ else ⊥

    10=10 : Eqℕ 10 10
    10=10 = tt
    
    10≠7 : ¬ Eqℕ 10 7
    10≠7 = λ e → e

    7≠10 : ¬ Eqℕ 7 10
    7≠10 = λ e → e


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
    comm× = λ A B → ((λ w → π₂ w , π₁ w) , (λ w → π₂ w , π₁ w))

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
    * if `t : Σ A B` then `π₁ t : A`
    * if `t : Σ A B` then `π₂ t : B (π₁ t)`
 * computation:
    * `π₁ (u , v) = u`
    * `π₂ (u , v) = v`
 * uniqueness:
    * `(λ x → t x) = t`

`A × B` can be defined as `Σ A (λ _ → B)`.

Example:

    w : Σ ℕ (λ n → Eqℕ (suc zero + n) (suc (suc (suc zero))))
    w = (suc (suc zero) , tt)

## Dependent elimination for `𝟚`, `ℕ` and `⊎`

Rules:

 * elimination:
    * `indℕ    : (P : ℕ     → Set) → P zero → ((n : ℕ) → P n → P (suc n)) → (t : ℕ) → P t`
    * `ind𝟚 : (P : 𝟚  → Set) → P tt → P ff → (t : 𝟚) → P t`
    * `ind⊎    : (P : A ⊎ B → Set) → ((a : A) → P (ι₁ a)) → ((b : B) → P (ι₂ b)) → (t : A ⊎ B) → P t`
 * computation:
    * `indℕ P u v zero = u`
    * `indℕ P u v (suc t) = v t (indℕ P u v t)`
    * `ind𝟚 P u v tt  = u`
    * `ind𝟚 P u v ff = v`
    * `ind⊎ P u v (ι₁ t) = u t`
    * `ind⊎ P u v (ι₂ t) = v t`

`rec`, `if_then_else`, `case` can be defined using `indℕ`,
`ind𝟚`, `ind⊎`, respectively.

Examples:

    ⊤s : (n : ℕ) → ⊤ ^ n
    ⊤s = indℕ (λ n → ⊤ ^ n) tt (λ n tts → tt , tts)

    notInvolutive : (x : 𝟚) → Eqb (not (not x)) x
    notInvolutive = λ x → ind𝟚 (λ x → Eqb (not (not x)) x) tt tt x

We want to prove `Eqb (not (not x)) x` for every `x : 𝟚`. We do
this by induction, that is, for every constructor for `𝟚` (`x =
tt` and `x = ff`) we have to show `Eqb (not (not x)) x`. In the
first case we need `Eqb (not (not tt)) tt = Eqb tt tt = ⊤`, in
the second case we need `Eqb (not (not ff)) ff = Eqb ff ff
= ⊤`. So we prove both cases simply be `tt`.

We show that `zero` is a left and right identity of addition.

    plusLeftId : (x : ℕ) → Eqℕ (plus zero x) x
    plusLeftId = λ x → indℕ (λ x → Eqℕ x x) tt (λ _ e → e) x

First we note that `Eqℕ (plus zero x) x = Eqℕ x x`. So we only have to
prove `Eqℕ x x` for every `x : ℕ`. Induction says that we have to
prove this first for `x = zero`, that is `Eqℕ zero zero = ⊤`, this is
easy: `tt`. Then, for any `n : ℕ`, given `e : Eqℕ n n`, we have to
show `Eqℕ (suc n) (suc n)`. `e` is called the inductive
hypothesis. But as we remarked above, `Eqℕ (suc n) (suc n) = Eqℕ n n`,
so we can direcly reuse the induction hypothesis to prove the case for
`x = suc n`.

## Predicate logic

A predicate (unary relation) on a type `A` has type `A → Set`. A binary relation written `R ⊂ A × B` in set theory is `R : A → B → Set` in Agda. `R a b` is the type of witnesses of the relation for `a : A` and `b : B`.

Universal and existential quantifiers can also be translated to types:

| logic                         | translation                            |
|:-----------------------------:|:--------------------------------------:|
| implication                   | `⟦ P ⇒ Q ⟧   	 := ⟦ P ⟧ → ⟦ Q ⟧`     	 |
| conjunction                   | `⟦ P ∧ Q ⟧   	 := ⟦ P ⟧ × ⟦ Q ⟧`     	 |
| tt                            | `⟦ Tt ⟧    	 := ⊤`                 	 |
| ff                            | `⟦ Ff ⟧   	 := ⊥`                 	 |
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
       (A B : Set)                         → (A ⊎ B)                ↔ Σ 𝟚 (λ b → if b then A else B)

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

Exercises (source: Thorsten Altenkirch). Assume:

    People : Set
    Ann    : People
    Kate   : People
    Peter  : People
    Child  : People → People → Set

Then:

 * Define the HasChild predicate.
 * Formalise: Ann is not a child of Kate.
 * Formalise: there is someone with exactly one child.
 * Define the relation Parent.
 * Formalise: No one is the parent of everyone.
 * Prove that if Ann has no children then Kate is not the child of Ann.


## Properties of `ℕ` and pattern matching

Addition:

    _+_ : ℕ → ℕ → ℕ
    _+_ = λ x y → rec y (λ _ n → suc n) x

A shorter notation for this in Agda:

    x + y = rec y (λ _ n → suc n) x

Pattern matching definition:

    zero  + y = y
    suc x + y = suc (x + y)

Note that this contains the same amount of information as the
`rec` variant and its behaviour is the same. Similarly, equality
of natural numbers can be redefined this way:

    eq : ℕ → ℕ → 𝟚
    eq zero    zero    = tt
    eq (suc x) zero    = ff
    eq zero    (suc y) = ff
    eq (suc x) (suc y) = eq x y

    toSet : 𝟚 → Set
    toSet tt  = ⊤
    toSet ff = ⊥

    Eqℕ : ℕ → ℕ → Set
    Eqℕ x y = toSet (eq x y)

Every such pattern matching definition can be rewritten into a
definition using `rec` or `indℕ`. Hardcore people only use the
eliminators, lazy people use pattern matching.

Properties of this equality:

    refl : (x : ℕ) → Eqℕ x x
    refl zero = tt
    refl (suc x) = refl x

    transport : (P : ℕ → Set)(x y : ℕ) → Eqℕ x y → P x → P y
    transport P zero    zero    e u = u
    transport P (suc x) zero    e u = exfalso e
    transport P zero    (suc y) e u = exfalso e
    transport P (suc x) (suc y) e u = transport (λ x → P (suc x)) x y e u

    sym : (x y : ℕ) → Eqℕ x y → Eqℕ y x
    sym x y e = transport (λ z → Eqℕ z x) x y e (refln x)

    trans : (x y z : ℕ) → Eqℕ x y → Eqℕ y z → Eqℕ x z
    trans x y z e e' = transport (λ q → Eqℕ x q) y z e' e

    cong : (f : ℕ → ℕ)(x y : ℕ) → Eqℕ x y → Eqℕ (f x) (f y)
    cong f x y e = transport (λ y → Eqℕ (f x) (f y)) x y e (refln (f x))
    
`zero` and `suc` are disjoint and successor is injective:

    zero≠suc : (x : ℕ) → ¬ Eqℕ zero (suc x)
    zero≠suc x e = e

    suc-ι : (x y : ℕ) → Eqℕ (suc x) (suc y) → Eqℕ x y
    suc-ι x y e = e

Natural numbers form a commutative monoid with `_+_` and `zero`.

    idl : (x : ℕ) → Eqℕ (zero + x) x
    idl x = refln x

    idr : (x : ℕ) → Eqℕ (x + zero) x
    idr zero    = tt
    idr (suc x) = idr x

    ass : (x y z : ℕ) → Eqℕ ((x + y) + z) (x + (y + z))
    ass zero    y z = refln (y + z)
    ass (suc x) y z = ass x y z

    comm-lemm : (x y : ℕ) → Eqℕ (suc x + y) (x + suc y)
    comm-lemm zero    y = refln y
    comm-lemm (suc x) y = comm-lemm x y

    comm : (x y : ℕ) → Eqℕ (x + y) (y + x)
    comm zero y    = sym (y + zero) y (idr y)
    comm (suc x) y = trans (suc (x + y)) (suc (y + x)) (y + suc x) (comm x y) (comm-lemm y x)

Prove `Eqℕ ((x + y) ^ 2) (x ^ 2 + 2 * x * y + y ^ 2)` using the
algebraic laws, `cong` and `trans`.

In the tutorials, show that natural numbers form a commutative
semiring with `+` and `*`. You can follow the [discrete math
textbook](https://bitbucket.org/akaposi/ttt/raw/master/muveletek_termeszetes_szamokkal.pdf).

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
    ≤dec zero y = ι₁ tt
    ≤dec (suc x) zero = ι₂ tt
    ≤dec (suc x) (suc y) = ≤dec x y

## Functions on vectors

    _^_ : Set → ℕ → Set
    A ^ zero  = ⊤
    A ^ suc x = A × A ^ x

`nil`, `cons`, `head`, `tail`, `++`

    count : (n : ℕ) → ℕ ^ n
    count zero = tt
    count (suc n) = n , count n

    _∧_ : 𝟚 → 𝟚 → 𝟚
    tt  ∧ tt = tt
    _     ∧ _    = ff

    eq^ : (l : ℕ) → ℕ ^ l → ℕ ^ l → 𝟚
    eq^ zero xs ys = tt
    eq^ (suc l) (x , xs) (y , ys) = eq x y ∧ eq^ l xs ys

    Eq^ : (l : ℕ) → ℕ ^ l → ℕ ^ l → Set
    Eq^ l xs ys = toSet (eq^ l xs ys)

    test-count : Eq^ 3 (count 3) (2 , 1 , 0 , tt)
    test-count = tt

    insert : ℕ → (l : ℕ) → ℕ ^ l → ℕ ^ (suc l)
    insert y zero    xs       = y , tt
    insert y (suc l) (x , xs) = case (≤dec y x)
      (λ _ → y , x , xs)
      (λ _ → x , insert y l xs)

    test-insert : Eq^ 5 (insert 3 4 (1 , 2 , 4 , 5 , tt)) (1 , 2 , 3 , 4 , 5 , tt)
    test-insert = tt

    sort : (l : ℕ) → ℕ ^ l → ℕ ^ l
    sort zero _ = tt
    sort (suc l) (x , xs) = insert x l (sort l xs)

    test-sort : Eq^ 5 (sort 5 (3 , 2 , 1 , 5 , 4 , tt)) (1 , 2 , 3 , 4 , 5 , tt)
    test-sort = tt

    Ordered : ℕ → (l : ℕ) → ℕ ^ l → Set
    Ordered b zero tt          = ⊤
    Ordered b (suc l) (x , xs) = b ≤ x × Ordered x l xs

    ins-ord : (l : ℕ)(xs : ℕ ^ l)(b : ℕ) → Ordered b l xs → (y : ℕ) → b ≤ y →
      Ordered b (suc l) (insert y l xs)
    ins-ord zero    xs       b tt               y b≤y = b≤y , tt
    ins-ord (suc l) (x , xs) b (b≤x , ord-x-xs) y b≤y = ind⊎
      (λ w → Ordered b (2 + l) (case w (λ _ → y , x , xs) (λ _ → x , insert y l xs)))
      (λ y≤x → b≤y , y≤x , ord-x-xs)
      (λ x≤y → b≤x , ins-ord l xs x ord-x-xs y x≤y)
      (≤dec y x) 

    sort-ord : (l : ℕ)(xs : ℕ ^ l) → Ordered 0 l (sort l xs)
    sort-ord zero xs = tt
    sort-ord (suc l) (x , xs) = ins-ord l (sort l xs) 0 (sort-ord l xs) x tt

    ∈ : (y : ℕ)(l : ℕ)(xs : ℕ ^ l) → Set
    ∈ y zero    tt       = ⊥
    ∈ y (suc l) (x , xs) = Eqℕ y x ⊎ ∈ y l xs

    ins-∈ : (y : ℕ)(l : ℕ)(xs : ℕ ^ l) → ∈ y (suc l) (insert y l xs)
    ins-∈ y zero xs = ι₁ (Eq-refl y)
    ins-∈ y (suc l) (x , xs) = ind⊎
      (λ w → ∈ y (suc (suc l)) (case w (λ _ → y , x , xs) (λ _ → x , insert y l xs)))
      (λ y≤x → ι₁ (Eq-refl y))
      (λ x≤y → ι₂ (ins-∈ y l xs))
      (≤dec y x)

    ins-other : (y z l : ℕ)(xs : ℕ ^ l) → ∈ y l xs → ∈ y (suc l) (insert z l xs)
    ins-other y z (suc l) (x , xs) y∈x,xs = ind⊎
      (λ w → ∈ y (suc (suc l)) (case w (λ _ → z , x , xs) (λ _ → x , insert z l xs)))
      (λ z≤x → ι₂ y∈x,xs)
      (λ x≤z → case y∈x,xs ι₁ λ y∈xs → ι₂ (ins-other y z l xs y∈xs))
      (≤dec z x)

    sort-∈ : (y : ℕ)(l : ℕ)(xs : ℕ ^ l) → ∈ y l xs → ∈ y l (sort l xs)
    sort-∈ y (suc l) (x , xs) (ι₁ y=x)  = transport (λ x → ∈ y (suc l) (sort (suc l) (x , xs))) y x y=x (ins-∈ y l (sort l xs))
    sort-∈ y (suc l) (x , xs) (ι₂ y∈xs) = ins-other y x l _ (sort-∈ y l xs y∈xs)

## Isomorphisms internally

    Eq𝟚→ℕ : (𝟚 → ℕ) → (𝟚 → ℕ) → Set
    Eq𝟚→ℕ f₀ f₁ = (x : 𝟚) → Eqℕ (f₀ x) (f₁ x)

    Eqℕ×ℕ : ℕ × ℕ → ℕ × ℕ → Set
    Eqℕ×ℕ u v = Eqℕ (π₁ u) (π₁ v) × Eqℕ (π₂ u) (π₂ v)

    α : (𝟚 → ℕ) → ℕ × ℕ
    α f = f tt , f ff

    β : ℕ × ℕ → (𝟚 → ℕ)
    β u = λ b → if b then π₁ u else π₂ u

    αβ : (u : ℕ × ℕ) → Eqℕ×ℕ (α (β u)) u
    αβ (a , b) = Eq-refl a , Eq-refl b

    βα : (f : 𝟚 → ℕ) → Eq𝟚→ℕ (β (α f)) f
    βα f tt  = Eq-refl (f tt)
    βα f ff = Eq-refl (f ff)
