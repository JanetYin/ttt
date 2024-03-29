{-# OPTIONS --safe --guardedness #-}

module Lib.CoFin.Literals where

open import Agda.Builtin.FromNat public
open import Lib.CoFin.Type
open import Lib.Conat.Type
open import Lib.Conat.Base
open import Lib.Nat.Type
open import Lib.Maybe.Type
open import Lib.Empty.Type
open import Lib.Unit.Type

instance
  NumCoFin : {n : ℕ∞} → Number (CoFin (succ∞ n))
  Number.Constraint (NumCoFin {n}) k = k ℕ≤ℕ∞ n
  Number.fromNat (NumCoFin {n}) zero ⦃ inst ⦄ = cofin nothing
  fpred∞ (Number.fromNat (NumCoFin {n}) (suc k) ⦃ inst ⦄) with pred∞ n
  ... | just n' = just {!!}
