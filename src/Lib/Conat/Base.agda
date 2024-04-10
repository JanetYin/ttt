{-# OPTIONS --safe --guardedness #-}

module Lib.Conat.Base where

open import Lib.Conat.PatternSynonym
open import Lib.Conat.Type
open import Lib.Sum.Type
open import Lib.Unit.Type
open import Lib.Empty.Type
open import Lib.Sigma.Type
open import Lib.Sigma.Base
open import Lib.Nat.Type
open import Lib.Equality
open import Lib.Maybe.Type
open import Lib.Maybe.Base

open import Lib.Bool.Type
open import Lib.Bool.Base
open import Lib.Containers.CoList

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
_*_ : ℕ∞ → ℕ∞ → ℕ∞
_*'_ : Maybe ℕ∞ → ℕ∞ → Maybe ℕ∞
suc∞ x *' k = just (k + x * k)
zero∞ *' k = nothing
pred∞ (n * k) = pred∞ n *' k
-}

add : ℕ∞ → ℕ∞ → ℕ∞
add n k = coiteℕ∞ (f k) (inl n) where
  f : ℕ∞ → ℕ∞ ⊎ ℕ∞ → Maybe (ℕ∞ ⊎ ℕ∞)
  f k (inl n) with pred∞ n
  ... | just n' = just (inl n')
  ... | nothing with pred∞ k
  ... | just k' = just (inr k')
  ... | nothing = nothing
  f _ (inr k) with pred∞ k
  ... | just k' = just (inr k')
  ... | nothing = nothing

infixl 7 _*_

_*_ : ℕ∞ → ℕ∞ → ℕ∞
n * k = coiteℕ∞ (f k) (n , k) where
  f : ℕ∞ → ℕ∞ × ℕ∞ → Maybe (ℕ∞ × ℕ∞)
  f restore (e1 , e2) with pred∞ e1
  ... | nothing = nothing
  ... | just e1' with pred∞ e2
  ... | nothing = nothing
  ... | just e2' with pred∞ e2'
  ... | nothing = just (e1' , restore)
  ... | just e2'' = just (e1 , e2')

infixr 8 _^_
-- Credits to Szumi for defining exponentiation
_^_ : ℕ∞ → ℕ∞ → ℕ∞
pred∞ (x ^ y) with pred∞ y
pred∞ (x ^ y) | nothing = just (embed 0)
pred∞ (x ^ y) | just y₁ with pred∞ x
pred∞ (x ^ y) | just y₁ | nothing = nothing
pred∞ (x ^ y) | just y₁ | just x₁ = just (coiteℕ∞ (λ (n , x₂ , xs₂) → step n x₂ xs₂) (0 ,' x₁ ,' coreplicate y₁ x₁))
  where
  step : ℕ → ℕ∞ → CoList ℕ∞ → Maybe (ℕ × ℕ∞ × CoList ℕ∞)
  step zero x₂ xs₂ with pred∞ x₂
  step zero x₂ xs₂ | nothing = nothing
  step zero x₂ xs₂ | just x₃ = just (1 , x₃ , xs₂)
  step (suc n) x₂ xs₂ with pred∞ x₂
  step (suc n) x₂ xs₂ | nothing with uncons xs₂
  step (suc n) x₂ xs₂ | nothing | nothing = nothing
  step (suc n) x₂ xs₂ | nothing | just (x₃ , xs₃) with step n x₃ xs₃
  step (suc n) x₂ xs₂ | nothing | just (x₃ , xs₃) | nothing = nothing
  step (suc n) x₂ xs₂ | nothing | just (x₃ , xs₃) | just (n₁ , x₄ , xs₄) = just (suc n₁ , x₁ , x₄ ∷ xs₄)
  step (suc n) x₂ xs₂ | just x₃ = just (suc n , x₃ , xs₂)

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
