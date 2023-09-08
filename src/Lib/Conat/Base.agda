{-# OPTIONS --safe --guardedness #-}

module Lib.Conat.Base where

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
... | inl _ = ⊤ , inl refl
... | inr _ = ⊥ , inr refl

IsZero∞ : ℕ∞ → Set
IsZero∞ n = fst (IsZero∞ᵗ n)

IsNotZero∞ᵗ : ℕ∞ → Σ Set (λ A → A ≡ ⊤ ⊎ A ≡ ⊥)
IsNotZero∞ᵗ n with pred∞ n
... | inl _ = ⊥ , inr refl
... | inr _ = ⊤ , inl refl

IsNotZero∞ : ℕ∞ → Set
IsNotZero∞ n = fst (IsNotZero∞ᵗ n)

conat : ℕ∞' → ℕ∞
pred∞ (conat a) = a

succ∞ : ℕ∞ → ℕ∞
pred∞ (succ∞ a) = inr a

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

∞ : ℕ∞
pred∞ ∞ = suc∞ ∞

infixl 6 _+_ _+′_
_+_ : ℕ∞ → ℕ∞ → ℕ∞
_+′_ : ℕ∞' → ℕ∞ → ℕ∞'

pred∞ (x + y) = pred∞ x +′ y
zero∞ +′ y = pred∞ y
suc∞ x +′ y = suc∞ (x + y)

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

coiteℕ∞ : ∀{i}{B : Set i} → (B → ⊤ ⊎ B) → B → ℕ∞
pred∞ (coiteℕ∞ f b) with f b
... | zero∞ = zero∞
... | suc∞ c = suc∞ (coiteℕ∞ f c)