{-# OPTIONS --safe #-}

module Lib.Nat.Instances.Eq where

open import Lib.Nat.Instances.DecidableEquality
open import Lib.Dec.InstanceGenerators.Eq
open import Lib.Class.Eq
open import Lib.Nat.Type

instance
  Eqℕ : Eq ℕ
  Eqℕ = DecidableEquality→Eq DecEqℕ
