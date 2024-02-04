{-# OPTIONS --safe #-}

module Lib.Nat.Instances.Ord where

open import Lib.Nat.Type
open import Lib.Nat.Instances.Eq
open import Lib.Ordering
open import Lib.Class.Ord

instance
  Ordℕ : Ord ℕ
  Ord.eq Ordℕ = Eqℕ
  Ord.compare Ordℕ zero zero = EQ
  Ord.compare Ordℕ zero (suc y) = LT
  Ord.compare Ordℕ (suc x) zero = GT
  Ord.compare Ordℕ (suc x) (suc y) = compare x y
