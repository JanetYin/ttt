{-# OPTIONS --safe --guardedness #-}

module Lib.Containers.CoVector.Type where

open import Lib.Conat.Type
open import Lib.Conat.Base

infixr 5 _∷_
record CoVec {ℓ}(A : Set ℓ) (n : ℕ∞) : Set ℓ where
  coinductive
  constructor _∷_
  field
    head : .⦃ IsNotZero∞ n ⦄ → A
    tail : .⦃ IsNotZero∞ n ⦄ → CoVec A (pred∞'' (pred∞ n))

open CoVec public