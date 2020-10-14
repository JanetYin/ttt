module tut.gy05 where

open import lib

-- you have to decide:
Dec : ∀{i} → Set i → Set i
Dec A = A ⊎ ¬ A

e1 : {X Y : Set} → Dec (X ⊎ Y → ¬ ¬ (Y ⊎ X))
e1 = ?

e2 : {X : Set} → Dec (¬ (X ⊎ ¬ X))
e2 = ?

e3 : {X : Set} → Dec (¬ (X → (¬ X → X)))
e3 = ?

e4 : Dec ℕ
e4 = ?

e5 : Dec ⊥
e5 = ?

e6 : {X : Set} → Dec (⊥ → X ⊎ ¬ X)
e6 = ?

e7 : {X : Set} → Dec (X × ¬ X → ¬ X ⊎ X)
e7 = ?

e8 : {X : Set} → Dec ((X → X) → ⊥)
e8 = ?

f1 : {X Y : Set} → ¬ ¬ X ⊎ ¬ ¬ Y → ¬ ¬ (X ⊎ Y)
f1 = ?

f2 : ({X Y : Set} → ¬ (X × Y) → ¬ X ⊎ ¬ Y) → {X Y : Set} → ¬ ¬ (X ⊎ Y) → ¬ ¬ X ⊎ ¬ ¬ Y
f2 = ?

-- no chance:
-- f3 : {X Y : Set} → Dec (X ⊎ Y → Y)
-- f3 = {!!}

-- because:
module f3a where
  X = ⊥
  Y = ⊤
  p : Dec (X ⊎ Y → Y)
  p = inj₁ λ _ → tt

module f3b where
  X = ⊤
  Y = ⊥
  p : Dec (X ⊎ Y → Y)
  p = inj₂ λ w → w (inj₁ tt)

-- higher order logic:

-- but:
f4 : Dec ((X Y : Set) → X ⊎ Y → Y)
f4 = ?

f5 : Dec ((X Y Z : Set) → (X → Z) ⊎ (Y → Z) → (X ⊎ Y → Z))
f5 = ?

f6 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f6 = ?

f7 : Dec ((X Y Z : Set) → (X × Y → Z) → (X → Z) × (Y → Z))
f7 = ?

f8 : Dec ((X Y Z : Set) → (X ⊎ Y × Z) → (X ⊎ Y) × (X ⊎ Z))
f8 = ?

f9 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → (X ⊎ Y × Z))
f9 = ?

f10 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → ((X ⊎ Y) × Z))
f10 = ?
