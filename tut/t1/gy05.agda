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

-- minden állításra: (x ⊃ z) ∨ (y ⊃ z) ⊃ (x ∨ y ⊃ z)
f5 : Dec ((X Y Z : Set) → (X → Z) ⊎ (Y → Z) → (X ⊎ Y → Z))
f5 = inj₂ λ t → t ⊤ ⊥ ⊥ (inj₂ (λ x → x)) (inj₁ tt) 

-- (x ⊃ z) ∧ (y ⊃ z) ⊃ (x ∧ y ⊃ z)
f6 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f6 = inj₁ λ X Y Z t u → proj₁ t (proj₁ u)

-- (x ∧ y ⊃ z) ⊃ (x ⊃ z) ∧ (y ⊃ z)
f7 : Dec ((X Y Z : Set) → (X × Y → Z) → (X → Z) × (Y → Z))
f7 = inj₂ λ t → proj₁ (t ⊤ ⊥ ⊥ proj₂) tt  

f8 : Dec ((X Y Z : Set) → (X ⊎ (Y × Z)) → (X ⊎ Y) × (X ⊎ Z))
f8 = inj₁ λ X Y Z t → case t inj₁ (λ u → inj₂ (proj₁ u)) , case t inj₁ λ u → inj₂ (proj₂ u)

f9 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → (X ⊎ Y × Z))
f9 = inj₁ λ X Y Z t → case (proj₁ t) inj₁ (case (proj₂ t) (λ x _ → inj₁ x) λ z y → inj₂ (y , z))

f10 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → ((X ⊎ Y) × Z))
f10 = inj₂ λ t → proj₂ (t ⊤ ℕ ⊥ ((inj₁ tt) , (inj₁ tt)))
