{-# OPTIONS --safe --guardedness #-}

module Lib.Conat.Type where

open import Lib.Unit.Type
open import Lib.Maybe.Type

record ℕ∞ : Set where
  coinductive
  constructor conat'
  field
    pred∞ : Maybe ℕ∞

open ℕ∞ public

∞ : ℕ∞
pred∞ ∞ = just ∞
{-
record ℕ∞ : Set

ℕ∞' : Set
ℕ∞' = ⊤ ⊎ ℕ∞

record ℕ∞ where
  coinductive
  constructor conat'
  field
    pred∞ : ℕ∞'
  
  pattern zero∞ = inl tt
  pattern suc∞ n = inr n

open ℕ∞ public
-}