{-# OPTIONS --safe #-}

module Lib.Fin.Literals where

open import Agda.Builtin.FromNat public
open import Lib.Fin.Type
open import Lib.Nat.Type
open import Lib.Nat.Base
open import Lib.Nat.Literals
open import Lib.Unit.Type public

instance
  NumFin : {n : ℕ} → Number (Fin (suc n))
  Number.Constraint (NumFin {n}) m = m ≤ℕ n
  Number.fromNat (NumFin {n}) zero = zero
  Number.fromNat (NumFin {suc n}) (suc m) = suc (Number.fromNat (NumFin {n}) m)