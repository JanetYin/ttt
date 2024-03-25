{-# OPTIONS --safe --guardedness #-}
module Lib.CoFin.Base where

open import Lib.CoFin.Type
open import Lib.Conat
open import Lib.Maybe.Type

f∞ : CoFin ∞
inz f∞ = tt
fpred∞ f∞ = just f∞

-- todo miafasz
coiteCoFin : ∀{ℓ}{n : ℕ∞}(P : ℕ∞ → Set ℓ) →
  (ginz : ({n : ℕ∞} → P n → IsNotZero∞ n)) →
  (gfpred∞ : {n : ℕ∞} → P n → Maybe (P (pred∞'' (pred∞ n)))) →
  (seed : P n) →
  CoFin n
inz (coiteCoFin P ginz gfpred∞ seed) = ginz seed
fpred∞ (coiteCoFin P ginz gfpred∞ seed) with gfpred∞ seed
... | just x = just (coiteCoFin P ginz gfpred∞ x)
... | nothing = nothing

cf1 : CoFin 1
cf1 = coiteCoFin IsNotZero∞ (λ z → z) (λ x → nothing) tt
