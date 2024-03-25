{-# OPTIONS --safe --guardedness #-}
module Lib.CoFin.Type where

open import Lib.Conat.Base
open import Lib.Conat.Literals
open import Lib.Conat.Type
open import Lib.Maybe.Type
open import Lib.Empty.Type

record CoFin (n : ℕ∞) : Set where
  coinductive
  constructor cofin
  field
    ⦃ inz ⦄ : IsNotZero∞ n
    fpred∞ : Maybe (CoFin (pred∞'' (pred∞ n)))

open CoFin public

coz : CoFin 0 → ⊥
coz x with inz x
... | ()
