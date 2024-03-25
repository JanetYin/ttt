{-# OPTIONS --safe --guardedness #-}

module Lib.Conat.Base where

open import Lib.Conat.PatternSynonym
open import Lib.Conat.Type
open import Lib.Sum.Type
open import Lib.Unit.Type
open import Lib.Empty.Type
open import Lib.Sigma.Type
open import Lib.Nat.Type
open import Lib.Equality
open import Lib.Maybe.Type

IsZero∞ᵗ : ℕ∞ → Σ Set (λ A → A ≡ ⊤ ⊎ A ≡ ⊥)
IsZero∞ᵗ n with pred∞ n
... | nothing = ⊤ , inl refl
... | just _ = ⊥ , inr refl

IsZero∞ : ℕ∞ → Set
IsZero∞ n = fst (IsZero∞ᵗ n)

IsNotZero∞ᵗ : ℕ∞ → Σ Set (λ A → A ≡ ⊤ ⊎ A ≡ ⊥)
IsNotZero∞ᵗ n with pred∞ n
... | nothing = ⊥ , inr refl
... | just _ = ⊤ , inl refl

IsNotZero∞ : ℕ∞ → Set
IsNotZero∞ n = fst (IsNotZero∞ᵗ n)

ℕ∞→ℕ : ℕ → ℕ∞ → Maybe ℕ
ℕ∞→ℕ zero _ = nothing
ℕ∞→ℕ (suc n) c with pred∞ c
... | zero∞ = just 0
... | suc∞ b with ℕ∞→ℕ n b
... | nothing = nothing
... | just x = just (suc x)

embed : ℕ → ℕ∞
pred∞ (embed zero) = zero∞
pred∞ (embed (suc n)) = suc∞ (embed n)

cover : ℕ → ℕ∞
cover zero = ∞
cover (suc n) = embed n

coiteℕ∞ : ∀{i}{B : Set i} → (B → Maybe B) → B → ℕ∞
pred∞ (coiteℕ∞ f b) with f b
... | zero∞ = zero∞
... | suc∞ c = suc∞ (coiteℕ∞ f c)

succ∞ : ℕ∞ → ℕ∞
pred∞ (succ∞ a) = just a

conat : Maybe ℕ∞ → ℕ∞
pred∞ (conat a) = a

succ∞' : Maybe ℕ∞ → Maybe ℕ∞
succ∞' n = just λ where .pred∞ → n

pred∞' : Maybe ℕ∞ → Maybe ℕ∞
pred∞' nothing = nothing
pred∞' (just x)  = pred∞ x

pred∞'' : Maybe ℕ∞ → ℕ∞
pred∞ (pred∞'' nothing) = nothing
pred∞'' (just x) = x

predℕ∞ : (n : ℕ∞) → .⦃ IsNotZero∞ n ⦄ → ℕ∞
predℕ∞ n with pred∞ n
... | suc∞ x = x

infixl 6 _+_ _+'_
_+_ : ℕ∞ → ℕ∞ → ℕ∞
_+'_ : Maybe ℕ∞ → ℕ∞ → Maybe ℕ∞

pred∞ (x + y) = pred∞ x +' y
zero∞ +' y = pred∞ y
suc∞ x +' y = suc∞ (x + y)

infix 4 _ℕ≤ℕ∞_

_ℕ≤ℕ∞_ : ℕ → ℕ∞ → Set
zero ℕ≤ℕ∞ k = ⊤
suc n ℕ≤ℕ∞ k with pred∞ k
... | nothing = ⊥
... | just k' = n ℕ≤ℕ∞ k'

--------------------------------------------------
-- Older idea of Conat with ⊤ ⊎ _
--------------------------------------------------
{-
conat : ℕ∞' → ℕ∞
pred∞ (conat a) = a

succ∞' : ℕ∞' → ℕ∞'
succ∞' n = inr λ where .pred∞ → n

pred∞' : ℕ∞' → ℕ∞'
pred∞' (inl tt) = inl tt
pred∞' (inr x)  = pred∞ x

pred∞'' : ℕ∞' → ℕ∞
pred∞ (pred∞'' (inl tt)) = inl tt
pred∞'' (inr x) = x

Unwrap-pred : ℕ∞' → Set
Unwrap-pred (inl _) = ⊤
Unwrap-pred (inr _) = ℕ∞

unwrap-pred : (n : ℕ∞') → Unwrap-pred n
unwrap-pred (inl _) = _
unwrap-pred (inr x) = x

infixl 6 _+_ _+′_
_+_ : ℕ∞ → ℕ∞ → ℕ∞
_+′_ : ℕ∞' → ℕ∞ → ℕ∞'

pred∞ (x + y) = pred∞ x +′ y
zero∞ +′ y = pred∞ y
suc∞ x +′ y = suc∞ (x + y)
-}
