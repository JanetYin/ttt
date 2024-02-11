{-# OPTIONS --safe #-}

module Lib.Fin.Instances.Eq where

open import Lib.Fin.Type
open import Lib.Dec
open import Lib.Fin.Instances.DecidableEquality
open import Lib.Class.Eq

instance
  EqFin : ∀{n} → Eq (Fin n)
  EqFin = DecidableEquality→Eq DecEqFin