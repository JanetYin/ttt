module tut.t3.gy05 where

open import lib

-- you have to decide:
Dec : ∀{i} → Set i → Set i
Dec A = A ⊎ ¬ A

e1 : {X Y : Set} → Dec (X ⊎ Y → ¬ ¬ (Y ⊎ X))
e1 = inj₁ λ xy → λ nyx → nyx (case xy (λ x → inj₂ x) inj₁)

e2 : {X : Set} → Dec (¬ (X ⊎ ¬ X))
e2 = inj₂ λ nxnx → nxnx (inj₂ λ x → nxnx (inj₁ x))

e3 : {X : Set} → Dec (¬ (X → (¬ X → X)))
e3 = inj₂ λ nf → nf λ x nx → x 

e4 : Dec ℕ
e4 = inj₁ 1

e5 : Dec ⊥
e5 = inj₂ λ x → x

e6 : {X : Set} → Dec (⊥ → X ⊎ ¬ X)
e6 = inj₁ λ b → exfalso b

e7 : {X : Set} → Dec (X × ¬ X → ¬ X ⊎ X)
--e7 = inj₁ λ p → inj₁ (proj₂ p)
e7 = inj₁ λ p → inj₂ (proj₁ p)

e8 : {X : Set} → Dec ((X → X) → ⊥)
e8 = inj₂ λ n → n λ x → x

f1 : {X Y : Set} → ¬ ¬ X ⊎ ¬ ¬ Y → ¬ ¬ (X ⊎ Y)
f1 = λ nnxnny nxy → case nnxnny (λ nnx → nnx λ x → nxy (inj₁ x)) λ nny → nny λ y → nxy (inj₂ y)

f2 : ({X Y : Set} → ¬ (X × Y) → ¬ X ⊎ ¬ Y) → {X Y : Set} → ¬ ¬ (X ⊎ Y) → ¬ ¬ X ⊎ ¬ ¬ Y
f2 = λ dm {X} {Y} nnxy → dm {X = ¬ X}{Y = ¬ Y} λ nxny → nnxy λ xy → case xy (proj₁ nxny) (proj₂ nxny) 

-- no chance:
--f3 : {X Y : Set} → Dec (X ⊎ Y → Y)
--f3 = ?

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
f4 = inj₂ λ lem → lem ⊤ ⊥ (inj₁ tt)

f5 : Dec ((X Y Z : Set) → (X → Z) ⊎ (Y → Z) → (X ⊎ Y → Z))
f5 = inj₂ λ w → w ⊤ ⊥ ⊥ (inj₂ λ x → x) (inj₁ tt)

f6 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f6 = inj₁ λ X Y Z xzyz xy → proj₁ xzyz (proj₁ xy)

f7 : Dec ((X Y Z : Set) → (X × Y → Z) → (X → Z) × (Y → Z))
f7 = inj₂ λ w → proj₁ (w ⊤ ⊥ ⊥ λ tb → proj₂ tb) tt

f8 : Dec ((X Y Z : Set) → (X ⊎ Y × Z) → (X ⊎ Y) × (X ⊎ Z))
f8 = inj₁ λ X Y Z w → case w (λ x → inj₁ x , inj₁ x) λ yz → inj₂ (proj₁ yz) , inj₂ (proj₂ yz) 

f9 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → (X ⊎ Y × Z))
f9 = inj₁ λ X Y Z xyxz → case (proj₁ xyxz) (λ x → inj₁ x) λ y → case (proj₂ xyxz) inj₁ λ z → inj₂ (y , z)

f10 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → ((X ⊎ Y) × Z))
f10 = inj₂ λ w → proj₂ (w ⊤ ⊤ ⊥ (inj₁ tt , inj₁ tt))

--h1 : Dec ((X Y Z : Set) → X × Y → ¬ (X ⊎ Y))
--h1 = {!!}
