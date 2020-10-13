module tut.t1.gy05 where

open import lib
  
-- you have to decide:
Dec : ∀{i} → Set i → Set i
Dec A = A ⊎ ¬ A

e1 : {X Y : Set} → Dec (X ⊎ Y → ¬ ¬ (Y ⊎ X))
e1 = inj₁ λ u v → case u (λ x → v (inj₂ x))
                         (λ y → v (inj₁ y))

e2 : {X : Set} → Dec (¬ (X ⊎ ¬ X))
e2 = inj₂ λ u → u (inj₂ λ x → u (inj₁ x))

e3 : {X : Set} → Dec (¬ (X → (¬ X → X)))
e3 = inj₂ λ u → u λ x _ → x

e4 : Dec ℕ
e4 = inj₁ zero

e5 : Dec ⊥
e5 = inj₂ exfalso

e6 : {X : Set} → Dec (⊥ → X ⊎ ¬ X)
e6 = inj₁ exfalso

e7 : {X : Set} → Dec ((X × ¬ X) → (¬ X ⊎ X))
e7 = inj₁ λ u → exfalso (proj₂ u (proj₁ u))

e8 : {X : Set} → Dec ((X → X) → ⊥)
e8 = inj₂ λ u → u λ x → x

f1 : {X Y : Set} → ¬ ¬ X ⊎ ¬ ¬ Y → ¬ ¬ (X ⊎ Y)
f1 = λ u v → case u
                  (λ nnx → nnx λ x → v (inj₁ x))
                  λ nny → nny λ y → v (inj₂ y)

f2 : ({X Y : Set} → ¬ (X × Y) → ¬ X ⊎ ¬ Y) → {X Y : Set} → ¬ ¬ (X ⊎ Y) → ¬ ¬ X ⊎ ¬ ¬ Y
f2 = {!!}

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
f4 = inj₂ λ u → u ⊤ ⊥ (inj₁ tt)

f5 : Dec ((X Y Z : Set) → (X → Z) ⊎ (Y → Z) → (X ⊎ Y → Z))
f5 = {!!}

f6 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f6 = {!!}

f7 : Dec ((X Y Z : Set) → (X × Y → Z) → (X → Z) × (Y → Z))
f7 = {!!}

f8 : Dec ((X Y Z : Set) → (X ⊎ Y × Z) → (X ⊎ Y) × (X ⊎ Z))
f8 = {!!}

f9 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → (X ⊎ Y × Z))
f9 = {!!}

f10 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → ((X ⊎ Y) × Z))
f10 = {!!}
