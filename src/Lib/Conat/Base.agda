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
open import Lib.Maybe.Base

IsZero∞ᵗ : ℕ∞ → Σ Set (λ A → A ≡ ⊤ ⊎ A ≡ ⊥)
IsZero∞ᵗ n = ite-Maybe (λ _ → ⊥ , inr refl) (⊤ , inl refl) (pred∞ n)

IsZero∞ : ℕ∞ → Set
IsZero∞ n = fst (IsZero∞ᵗ n)

IsNotZero∞ᵗ : ℕ∞ → Σ Set (λ A → A ≡ ⊤ ⊎ A ≡ ⊥)
IsNotZero∞ᵗ n = ite-Maybe (λ _ → ⊤ , inl refl) (⊥ , inr refl) (pred∞ n)

IsNotZero∞ : ℕ∞ → Set
IsNotZero∞ n = fst (IsNotZero∞ᵗ n)

instance
  recomputeIsNotZero∞ : {n : ℕ∞} → .⦃ IsNotZero∞ n ⦄ → IsNotZero∞ n
  recomputeIsNotZero∞ {n} with pred∞ n
  ... | just _ = tt

pred∞withProof : (n : ℕ∞) → Σ (Maybe ℕ∞) (ite-Maybe (λ _ → IsNotZero∞ n) (IsZero∞ n))
pred∞withProof n with pred∞ n
... | suc∞ x = suc∞ x , tt
... | zero∞ = zero∞ , tt

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
pred∞' (just x) = pred∞ x

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

{-
infixl 7 _*_ _*'_

_*_ : ℕ∞ → ℕ∞ → ℕ∞
_*'_ : Maybe ℕ∞ → ℕ∞ → Maybe ℕ∞
suc∞ x *' k = just (k + x * k)
zero∞ *' k = nothing
pred∞ (n * k) = pred∞ n *' k
-}

add : ℕ∞ → ℕ∞ → ℕ∞
add n k = coiteℕ∞ f (n , k) where
  f : ℕ∞ × ℕ∞ → Maybe (ℕ∞ × ℕ∞)
  f (n , k) with pred∞ n
  ... | just n' = just (n' , k)
  ... | nothing with pred∞ k
  ... | just k' = just (n , k')
  ... | nothing = nothing

mul : ℕ∞ → ℕ∞ → ℕ∞
mul n k = coiteℕ∞ f (n , n , k) where
  f : ℕ∞ × ℕ∞ × ℕ∞ → Maybe (ℕ∞ × ℕ∞ × ℕ∞)
  f (restore , e2 , e3) with pred∞ e2 | pred∞ e3
  ... | suc∞ e2' | zero∞ = nothing
  ... | zero∞ | suc∞ e3' = nothing
  ... | zero∞ | zero∞ = nothing
  ... | suc∞ e2' | suc∞ e3' with pred∞ e2' | pred∞ e3'
  ... | suc∞ e2'' | suc∞ e3'' = just (restore , e2' , e3)
  ... | suc∞ e2'' | zero∞ = just (restore , e2' , e3)
  ... | zero∞ | suc∞ e3'' = just (restore , restore , e3')
  ... | zero∞ | zero∞ = just (restore , e2' , e3')


infix 4 _ℕ≤ℕ∞_

_ℕ≤ℕ∞_ : ℕ → ℕ∞ → Set
zero ℕ≤ℕ∞ k = ⊤
suc n ℕ≤ℕ∞ k with pred∞ k
... | nothing = ⊥
... | just k' = n ℕ≤ℕ∞ k'

infix 4 _ℕ<ℕ∞_

_ℕ<ℕ∞_ : ℕ → ℕ∞ → Set
n ℕ<ℕ∞ k with pred∞ k
(n ℕ<ℕ∞ k)     | zero∞ = ⊥
(zero ℕ<ℕ∞ k)  | suc∞ x = ⊤
(suc n ℕ<ℕ∞ k) | suc∞ x = n ℕ<ℕ∞ x

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
