{-# OPTIONS --safe #-}

module Lib.Class.Ord where

open import Lib.Level
open import Lib.Bool
open import Lib.Class.Eq
open import Lib.Ordering.Type

record Ord {i}(A : Set i) : Set (lsuc i) where
  constructor OrdInstance
  field
    overlap ⦃ eq ⦄ : Eq A
    compare : A → A → Ordering
  infix 4 _<=_ _<_ _>=_ _>_
  _<=_ : A → A → Bool
  x <= y with compare x y
  ... | LT = true
  ... | EQ = true
  ... | GT = false

  _<_ : A → A → Bool
  x < y with compare x y
  ... | LT = true
  ... | EQ = false
  ... | GT = false

  _>=_ : A → A → Bool
  x >= y with compare x y
  ... | LT = false
  ... | EQ = true
  ... | GT = true

  _>_ : A → A → Bool
  x > y with compare x y
  ... | LT = false
  ... | EQ = false
  ... | GT = true

open Ord {{...}} public
