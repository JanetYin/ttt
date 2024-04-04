{-# OPTIONS --safe --guardedness #-}

module Lib.CoFin.Type where

open import Lib.Conat.Base
open import Lib.Conat.Literals
open import Lib.Conat.Type
open import Lib.Maybe.Type
open import Lib.Empty.Type

open import Lib.Equality.Type

record CoFin (n : ℕ∞) : Set where
  coinductive
  constructor cofin
  field
    ⦃ inz ⦄ : IsNotZero∞ n
    fpred∞ : Maybe (CoFin (predℕ∞ n))

open CoFin public

coz : CoFin 0 → ⊥
coz = inz

proba : (n : ℕ∞) → .⦃ p1 p2 : IsNotZero∞ n ⦄ → CoFin n
proba n = cofin ⦃ recomputeIsNotZero∞ {n} ⦄ nothing
