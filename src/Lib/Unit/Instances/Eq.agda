{-# OPTIONS --safe #-}

module Lib.Unit.Instances.Eq where

open import Lib.Unit.Instances.DecidableEquality
open import Lib.Dec.InstanceGenerators
open import Lib.Class.Eq
open import Lib.Unit.Type

instance
  Eq⊤ : Eq ⊤
  Eq⊤ = DecidableEquality→Eq DecEq⊤