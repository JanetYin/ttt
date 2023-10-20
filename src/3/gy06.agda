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

-- \inf = \infty = ∞
0∞ : ℕ∞
pred∞ 0∞ = nothing

1∞ : ℕ∞
pred∞ 1∞ = just 0∞

2∞ : ℕ∞
pred∞ 2∞ = just 1∞

∞ : ℕ∞
pred∞ ∞ = just ∞

infixl 6 _+∞_
_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
pred∞ (n +∞ k) with pred∞ n
... | nothing = pred∞ k
... | just x = just (x +∞ k)

coiteℕ∞ : ∀{i}{B : Set i} → (B → Maybe B) → B → ℕ∞
pred∞ (coiteℕ∞ f b) with f b
... | just x = just (coiteℕ∞ f x)
... | nothing = nothing

IsNotZero∞ : ℕ∞ → Set
IsNotZero∞ n with pred∞ n
... | nothing  = ⊥
... | (just _) = ⊤

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
-- \{{ = ⦃
-- \}} = ⦄

[] : ∀{i}{A : Set i} → CoVec A 0
head [] ⦃ () ⦄
tail [] ⦃ () ⦄

[1] : CoVec ℕ 1
[1] = 1 ∷ []

replicate : ∀{i}{A : Set i} → (n : ℕ∞) → A → CoVec A n
head (replicate n a) = a
tail (replicate n a) with pred∞ n
... | just x = replicate x a

repeat : ∀{i}{A : Set i} → A → CoVec A ∞
repeat = replicate ∞

map : ∀{i j}{A : Set i}{B : Set j}{n : ℕ∞} → (A → B) → CoVec A n → CoVec B n
head (map f xs) = f (head xs)
tail (map f xs) = map f (tail xs)

------------------------------------------------------
-- Dependent isomorphisms -- lesz vizsgában
------------------------------------------------------

Σ=⊎ : {A B : Set} → Σ Bool (if_then A else B) ↔ A ⊎ B
Σ=⊎ = to , from where
  to : {A B : Set} → Σ Bool (if_then A else B) → A ⊎ B
  to (false , b) = inr b
  to (true , a) = inl a

  from : {A B : Set} → A ⊎ B → Σ Bool (if_then A else B)
  from (inl a) = true , a
  from (inr b) = false , b

Σ=× : {A B : Set} → Σ A (λ _ → B) ↔ A × B
Σ=× = (λ x → x) , (λ x → x)

Π=→ : {A B : Set} → ((a : A) → (λ _ → B) a) ≡ (A → B)
Π=→ = refl

→=× : {A B : Set} → ((b : Bool) → if b then A else B) ↔ A × B
→=× = to , from where
  to : {A B : Set} → ((b : Bool) → if b then A else B) → A × B
  to f = f true , f false

  from : {A B : Set} → A × B → ((b : Bool) → if b then A else B)
  from (a , b) false = b
  from (a , b) true = a

dependentCurry : {A : Set}{B : A → Set}{C : (a : A) → B a → Set} →
  ((a : A)(b : B a) → C a b) ↔ ((w : Σ A B) → C (fst w) (snd w))
dependentCurry = to , from where
  to : {A : Set}{B : A → Set}{C : (a : A) → B a → Set} → 
       ((a : A)(b : B a) → C a b) → ((w : Σ A B) → C (fst w) (snd w))
  to f (a , b) = f a b

  from : {A : Set}{B : A → Set}{C : (a : A) → B a → Set} →
         ((w : Σ A B) → C (fst w) (snd w)) → ((a : A)(b : B a) → C a b)
  from f a b = f (a , b)

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