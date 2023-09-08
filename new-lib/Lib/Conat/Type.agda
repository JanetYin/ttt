{-# OPTIONS --safe --guardedness #-}

module Lib.Conat.Type where

open import Lib.Unit.Type
open import Lib.Sum.Type

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