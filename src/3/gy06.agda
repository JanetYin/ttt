module gy06 where

open import Lib
  hiding (∞; _+∞_; IsNotZero∞; coiteℕ∞)
open import Lib.Containers.CoVector
  hiding ([]; repeat; replicate; map)

------------------------------------------------------
-- Conat -- lesz vizsgában
------------------------------------------------------

{-
record ℕ∞ : Set where
  coinductive
  constructor conat'
  field
    pred∞ : Maybe ℕ∞

open ℕ∞ public
-}

0∞ : ℕ∞
0∞ = {!   !}

1∞ : ℕ∞
1∞ = {!   !}

2∞ : ℕ∞
2∞ = {!   !}

∞ : ℕ∞
∞ = {!   !}

infixl 6 _+∞_
_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
n +∞ k = {!   !}

coiteℕ∞ : ∀{i}{B : Set i} → (B → Maybe B) → B → ℕ∞
coiteℕ∞ = {!   !}

IsNotZero∞ : ℕ∞ → Set
IsNotZero∞ n = {!   !}

------------------------------------------------------
-- CoVec -- NEM lesz vizsgában, csak érdekesség most.
------------------------------------------------------

{-
infixr 5 _∷_
record CoVec {ℓ}(A : Set ℓ) (n : ℕ∞) : Set ℓ where
  coinductive
  constructor _∷_
  field
    head : .⦃ IsNotZero∞ n ⦄ → A
    tail : .⦃ IsNotZero∞ n ⦄ → CoVec A (pred∞'' (pred∞ n))
-}

[] : ∀{i}{A : Set i} → CoVec A ?
[] = {!   !}

[1] : CoVec ℕ ?
[1] = ?

replicate : ∀{i}{A : Set i} → {!   !}
replicate = {!   !}

repeat : ∀{i}{A : Set i} → {!   !}
repeat = {!   !}

map : ∀{i j}{A : Set i}{B : Set j}{n : ℕ∞} → {!   !}
map = {!   !}

------------------------------------------------------
-- Dependent isomorphisms -- lesz vizsgában
------------------------------------------------------

Σ=⊎ : {A B : Set} → Σ Bool (if_then A else B) ↔ A ⊎ B
Σ=⊎ = {!!}

Σ=× : {A B : Set} → Σ A (λ _ → B) ↔ A × B
Σ=× = {!!}

Π=→ : {A B : Set} → ((a : A) → (λ _ → B) a) ≡ (A → B)
Π=→ = {!!}

→=× : {A B : Set} → ((b : Bool) → if b then A else B) ↔ A × B
→=× = {!!}

dependentCurry : {A : Set}{B : A → Set}{C : (a : A) → B a → Set} →
  ((a : A)(b : B a) → C a b) ↔ ((w : Σ A B) → C (fst w) (snd w))
dependentCurry = {!!}

∀×-distr  : {A : Set}{P : A → Set}{Q : A → Set} → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
∀×-distr = {!!}

-- this might be hard
Fin* : {m n : ℕ} → Fin (m * n) ↔ Fin m × Fin n
Fin* = {!!}

-- n-1
--  Σ  a i = a 0 + a 1 + ... + a (n-1)
-- i=0

Σℕ : (n : ℕ) → (Fin n → ℕ) → ℕ
Σℕ zero    a = 0
Σℕ (suc n) a = a zero + Σℕ n (λ i → a (suc i))

-- not very easy
Σ+ : (n : ℕ)(a : Fin n → ℕ) → Σ (Fin n) (λ i → Fin (a i)) ↔ Fin (Σℕ n a)
Σ+ = {!!}

-- n-1
--  Π  a i = a 0 * a 1 * ... * a (n-1)
-- i=0

Πℕ : (n : ℕ) → (Fin n → ℕ) → ℕ
Πℕ zero    a = 0
Πℕ (suc n) a = a zero * Πℕ n (λ i → a (suc i))

-- not very easy
Π* : (n : ℕ)(a : Fin n → ℕ) → ((i : Fin n) → Fin (a i)) ↔ Fin (Πℕ n a)
Π* = {!!}
