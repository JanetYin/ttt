open import lib

---------------------------------------------------------
-- higher order logic
------------------------------------------------------

Dec : ∀{i} → Set i → Set i
Dec A = A ⊎ ¬ A

f4 : Dec ((X Y : Type) → X ⊎ Y → Y)
f4 = {!!}

f5 : Dec ((X Y Z : Type) → (X → Z) ⊎ (Y → Z) → (X ⊎ Y → Z))
f5 = {!!}

f6 : Dec ((X Y Z : Type) → (X → Z) × (Y → Z) → (X × Y → Z))
f6 = {!!}

f7 : Dec ((X Y Z : Type) → (X × Y → Z) → (X → Z) × (Y → Z))
f7 = {!!}

f8 : Dec ((X Y Z : Type) → (X ⊎ Y × Z) → (X ⊎ Y) × (X ⊎ Z))
f8 = {!!}

f9 : Dec ((X Y Z : Type) → (X ⊎ Y) × (X ⊎ Z) → (X ⊎ Y × Z))
f9 = {!!}

f10 : Dec ((X Y Z : Type) → (X ⊎ Y) × (X ⊎ Z) → ((X ⊎ Y) × Z))
f10 = {!!}

---------------------------------------------------------
-- predicate (first order) logic example
---------------------------------------------------------

module People
  (Person    : Type)
  (Ann       : Person)
  (Kate      : Person)
  (Peter     : Person)
  (_childOf_ : Person → Person → Type)
  (_sameAs_  : Person → Person → Type) -- ez most itt az emberek egyenlosege
  where

  -- Define the _hasChild predicate.
  _hasChild : Person → Type
  x hasChild = {!!}

  -- Formalise: Ann is not a child of Kate.
  ANK : Type
  ANK = {!!}

  -- Formalise: there is someone with exactly one child.
  ONE : Type
  ONE = {!!}

  -- Define the relation _parentOf_.
  _parentOf_ : Person → Person → Type
  x parentOf y = {!!}

  -- Formalise: No one is the parent of everyone.
  NOPE : Type
  NOPE = {!!}

  -- Prove that if Ann has no children then Kate is not the child of Ann.
  AK : ¬ (Σ Person λ y → y childOf Ann) → ¬ (Kate childOf Ann)
  AK = {!!}

  -- Prove that if there is no person who is his own parent than no one is the parent of everyone.
  ¬NOPE : ¬ (Σ Person λ x → x parentOf x) → NOPE
  ¬NOPE = {!!}

---------------------------------------------------------
-- predicate (first order) logic laws
---------------------------------------------------------

∀×-distr  :    (A : Type)(P : A → Type)(Q : A → Type) → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
∀×-distr = {!!}
∀⊎-distr  :    (A : Type)(P : A → Type)(Q : A → Type) → ((a : A) → P a) ⊎ ((a : A) → Q a) → ((a : A) → P a ⊎ Q a)
∀⊎-distr = {!!}
Σ×-distr  :    (A : Type)(P : A → Type)(Q : A → Type) → (Σ A λ a → P a × Q a)  → Σ A P × Σ A Q
Σ×-distr = {!!}
Σ⊎-distr  :    (A : Type)(P : A → Type)(Q : A → Type) → (Σ A λ a → P a ⊎ Q a)  ↔ Σ A P ⊎ Σ A Q
Σ⊎-distr = {!!}
¬∀        :    (A : Type)(P : A → Type)              → (Σ A λ a → ¬ P a)      → ¬ ((a : A) → P a)
¬∀ = {!!}
¬Σ        :    (A : Type)(P : A → Type)              → (¬ Σ A λ a → P a)      ↔ ((a : A) → ¬ P a)
¬Σ = {!!}
⊎↔ΣBool   :    (A B : Type)                         → (A ⊎ B)                ↔ Σ Bool (λ b → if b then A else B)
⊎↔ΣBool = {!!}
¬¬∀-nat   :    (A : Type)(P : A → Type)              → ¬ ¬ ((x : A) → P x)    → (x : A) → ¬ ¬ (P x)
¬¬∀-nat = {!!}

∀⊎-distr' : ¬ ((A : Type)(P : A → Type)(Q : A → Type) → (((a : A) → P a ⊎ Q a) → ((a : A) → P a) ⊎ ((a : A) → Q a)))
∀⊎-distr' = {!!}

Σ×-distr' : ¬ ((A : Type)(P : A → Type)(Q : A → Type) → (Σ A P × Σ A Q → Σ A λ a → P a × Q a))
Σ×-distr' w = {!!}
 
Σ∀       : (A B : Type)(R : A → B → Type)        → (Σ A λ x → (y : B) → R x y) → (y : B) → Σ A λ x → R x y
Σ∀ = {!!}
AC       : (A B : Type)(R : A → B → Type)        → ((x : A) → Σ B λ y → R x y) → Σ (A → B) λ f → (x : A) → R x (f x)
AC = {!!}
