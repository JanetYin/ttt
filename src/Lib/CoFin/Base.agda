{-# OPTIONS --safe --guardedness #-}
module Lib.CoFin.Base where

open import Lib.CoFin.Type
open import Lib.Conat
open import Lib.Maybe
open import Lib.Sigma
open import Lib.Function
open import Lib.InstanceSigma.Type

f∞ : CoFin ∞
inz f∞ = tt
fpred∞ f∞ = just f∞


coiteCoFin : ∀{ℓ}{n : ℕ∞}(P : ℕ∞ → Set ℓ) →
  (ginz : ({n : ℕ∞} → P n → IsNotZero∞ n)) →
  (gfpred∞ : {n : ℕ∞} → (p : P n) → Maybe (P (predℕ∞ n ⦃ ginz p ⦄))) →
  (seed : P n) →
  CoFin n
inz (coiteCoFin P ginz gfpred∞ seed) = ginz seed
fpred∞ (coiteCoFin P ginz gfpred∞ seed) with gfpred∞ seed
... | just x = just (coiteCoFin P ginz gfpred∞ x)
... | nothing = nothing

opaque -- sztem segít
  coiteCoFinΣ : ∀{ℓ}{n : ℕ∞}(P : ℕ∞ → Set ℓ) →
    (gen : {n : ℕ∞} → P n → Σ (IsNotZero∞ n) λ p → Maybe (P (predℕ∞ n ⦃ p ⦄))) →
    (seed : P n) →
    CoFin n
  coiteCoFinΣ P gen seed = coiteCoFin P (fst ⊚ gen) (snd ⊚ gen) seed

  coiteCoFinιΣ : ∀{ℓ}{n : ℕ∞}(P : ℕ∞ → Set ℓ) →
    (gen : {n : ℕ∞} → P n → ιΣ (IsNotZero∞ n) (Maybe (P (predℕ∞ n)))) →
    (seed : P n) →
    CoFin n
  coiteCoFinιΣ P gen seed = coiteCoFinΣ P (fst ιΣ↔Σ ⊚ gen) seed
