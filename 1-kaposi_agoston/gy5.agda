module gy5 where

open import lib

infixl 3 _≡_

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

isZero : ℕ → Bool
isZero = λ n → primrec true (λ _ _ → false) n

not : Bool → Bool
not = λ b → if b then false else true

even : ℕ → Bool
even = λ n → primrec true (λ _ even' → not even') n

pred : ℕ → ℕ
pred = λ n → primrec zero (λ n' _ → n') n

-- Homeworks:
task0 : ((Y × X) × Z) → (Z × (X × Y))
task0 ={!!}

task1 : (Z × (X × Y)) → ((Y × X) × Z)
task1 = {!!}

task2 : ((Y × X) × Z) ↔ (Z × (X × Y))
task2 = {!!}

--microzh
ℕ-curry : (ℕ × ℕ → ℕ) → (ℕ → ℕ → ℕ)
ℕ-curry = {!!}

ℕ-uncurry : (ℕ → ℕ → ℕ) → (ℕ × ℕ → ℕ)
ℕ-uncurry = {!!}

ℕ-currying : (ℕ × ℕ → ℕ) ↔ (ℕ → ℕ → ℕ)
ℕ-currying = {!!}

---------------------------------------------------------
-- Abbreviated types
---------------------------------------------------------

currying : (X → Y → Z) ↔ (X × Y → Z)
currying = {!!}

→×distr-r : (X → Y) × (X → Z) → (X → Y × Z)
→×distr-r = {!!}

→×distr-l : (X → Y × Z) → (X → Y) × (X → Z)
→×distr-l = {!!}

→×distr : (X → Y) × (X → Z) ↔ (X → Y × Z)
→×distr = {!!}

---------------------------------------------------------
-- Coproducts
---------------------------------------------------------

-- how many implementations?
undiag : X ⊎ X → X
undiag = {!!}

×⊎distr : (X × Y) ⊎ Z → (X ⊎ Z) × (Y ⊎ Z)
×⊎distr = {!!}


test1 : ⊥ → ⊤
test1 = λ t → exfalso t
test2 : ⊥ → ⊤
test2 = λ x → tt

---------------------------------------------------------
-- Algebraic structure on types
---------------------------------------------------------

-- some of the following laws hold up to definitional isomorphism, not
-- only logical equivalence. We can test these in Agda by normalising
-- λ x → proj₁ ⊎ass (proj₂ ⊎ass x) etc.

-- ⊎ is a commutative monoid



⊎ass  : (X ⊎ Y) ⊎ Z ↔ X ⊎ (Y ⊎ Z)
⊎ass = {!!}

⊎lid  : ⊥ ⊎ X ↔ X
⊎lid = {!!}

⊎rid  : X ⊎ ⊥ ↔ X
⊎rid = {!!}

⊎comm : (X ⊎ Y) ↔ Y ⊎ X
⊎comm = {!!}
    
-- × is a commutative monoid with a null element
×ass  : (X × Y) × Z ↔ X × (Y × Z)
×ass = {!!}

×lid  : ⊤ × X ↔ X
×lid = {!!}

×rid  : X × ⊤ ↔ X
×rid = {!!}

×comm : (X × Y) ↔ Y × X
×comm = {!!}

×null : ⊥ × X ↔ ⊥
×null = {!!}

→lid : (⊤ → X) ↔ X
→lid = {!!}

→rnull : (X → ⊤) ↔ ⊤
→rnull = {!!}

→⊥⊤ : (⊥ → X) ↔ ⊤
→⊥⊤ = {!!}

-- distributivity laws
⊎×dist : (X ⊎ Y) × Z ↔ (X × Z) ⊎ (Y × Z)
⊎×dist = {!!}

×⊎dist : (X × Y) ⊎ Z ↔ (X ⊎ Z) × (Y ⊎ Z) -- this is not an isomorphism
×⊎dist = {!!}

⊎→dist : (X ⊎ Y) → Z ↔ (X → Z) × (Y → Z)
⊎→dist = {!!}

→×dist : X → (Y × Z) ↔ (X → Y) × (X → Z)
→×dist = {!!}

×→dist : (X × Y) → Z ↔ X → (Y → Z)
×→dist = {!!}

{-
---------------------------------------------------------
-- Logic
---------------------------------------------------------

-- negation

anything : ¬ X → X → Y

-- ¬¬ is a monad

¬¬return : X → ¬ ¬ X

¬¬join : ¬ ¬ ¬ ¬ X → ¬ ¬ X
¬¬join = λ nnnnx nx → nnnnx λ nnx → nnx nx

-- De Morgan (one direction does not work) and other negation stuff

¬⊎ : ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
¬⊎ = {!!}
¬× : ¬ (X × Y) ← ¬ X ⊎ ¬ Y
¬× = {!!}

nocontra : ¬ (X ↔ ¬ X)
nocontra = {!!}

¬¬dnp : ¬ ¬ (¬ ¬ X → X)
¬¬dnp = {!!}

build→ : ¬ X ⊎ Y → (X → Y)
build→ = {!!}

¬¬invol : ¬ ¬ ¬ X ↔ ¬ X
¬¬invol = {!!}
-}
