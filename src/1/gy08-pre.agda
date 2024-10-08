module gy08-pre where

open import Lib
-- open import Lib.Dec.PatternSynonym

------------------------------------------------------
-- statements as parameters
------------------------------------------------------

blowUp : ((A : Set) → ¬ A) → ⊥
blowUp f = {!!}
-- what's the difference with this?
-- (A : Set) → ¬ A → ⊥

-- something like this may appear in the exam

---------------------------------------------------------
-- predicate (first order) logic example
---------------------------------------------------------

notExists↔noneOf : ∀{i}{A : Set i} → (P : A → Set) →
                        ¬ (Σ A (λ x → P x)) ↔ (∀ x → ¬ (P x))
notExists↔noneOf = {!!}

module People
  (Person    : Set)
  (Ann       : Person)
  (Kate      : Person)
  (Peter     : Person)
  (_childOf_ : Person → Person → Set)
  (_sameAs_  : Person → Person → Set) -- ez most itt az emberek egyenlosege
  where

  -- Define the _hasChild predicate.
  _hasChild : Person → Set
  x hasChild = {!!}

  -- Formalise: Ann is not a child of Kate.
  ANK : Set
  ANK = {!!}

  -- Formalise: there is someone with exactly one child.
  ONE : Set
  ONE = {!!}

  -- Define the relation _parentOf_.
  _parentOf_ : Person → Person → Set
  x parentOf y = {!!}

  -- Formalise: No one is the parent of everyone.
  NOPE : Set
  NOPE = {!!}

  -- Prove that if Ann has no children then Kate is not the child of Ann.
  AK : ¬ (Σ Person λ y → y childOf Ann) → ¬ (Kate childOf Ann)
  AK = {!!}

  -- Prove that if there is no person who is his own parent than no one is the parent of everyone.
  ¬xpopxthenNOPE : ¬ (Σ Person λ x → x parentOf x) → NOPE
  ¬xpopxthenNOPE = {!!}

---------------------------------------------------------
-- predicate (first order) logic laws
---------------------------------------------------------

∀×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a × Q a) ↔ ((a : A) → P a) × ((a : A) → Q a)
fst (∀×-distr A P Q) = λ x → (λ a → fst (x a)) , (λ a → snd (x a ))
snd (∀×-distr A P Q) = λ x a → (fst x a) , (snd x a)

-- !!!
Σ⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a) ↔ Σ A P ⊎ Σ A Q
Σ⊎-distr = {!!}

-- !!!
∀⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a) ⊎ ((a : A) → Q a) → ((a : A) → P a ⊎ Q a)
∀⊎-distr = {!!}
-- ez miért csak odafelé megy?
-- miért nem ↔ van közte?

-- !!!
∀⊎-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (((a : A) → P a ⊎ Q a) → ((a : A) → P a) ⊎ ((a : A) → Q a)))
∀⊎-distr' = {!!}

-- !!!
Σ×-distr  : Dec ((A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a × Q a)  → Σ A P × Σ A Q)
Σ×-distr = {!!}

-- !!!
Σ×-distr' : Dec ((A : Set)(P : A → Set)(Q : A → Set) → (Σ A P × Σ A Q → Σ A λ a → P a × Q a))
Σ×-distr' = {!!}

¬∀        :    (A : Set)(P : A → Set)              → (Σ A λ a → ¬ P a)      → ¬ ((a : A) → P a)
¬∀ A P x x₁ = snd x (x₁ (fst x))

-- Ugyanez van a fájl tetején is:
¬Σ        :    (A : Set)(P : A → Set)              → (¬ Σ A λ a → P a)      ↔ ((a : A) → ¬ P a)
fst (¬Σ A P) = λ x a x₁ → {!   !}
snd (¬Σ A P) = λ x x₁ → {!   !}

¬¬∀-nat   :    (A : Set)(P : A → Set)              → ¬ ¬ ((x : A) → P x)    → (x : A) → ¬ ¬ (P x)
¬¬∀-nat = {!!}
 
Σ∀       : (A B : Set)(R : A → B → Set)        → (Σ A λ x → (y : B) → R x y) → (y : B) → Σ A λ x → R x y
Σ∀ = {!!}

AC       : (A B : Set)(R : A → B → Set)        → ((x : A) → Σ B λ y → R x y) → Σ (A → B) λ f → (x : A) → R x (f x)
AC = {!!}
