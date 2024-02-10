{-# OPTIONS --safe #-}

module Lib.Empty.Instances.Eq where

open import Lib.Class.Eq

open import Lib.Empty.Instances.DecidableEquality

open import Lib.Empty.Type

open import Lib.Dec

instance
  Eq⊥ : Eq ⊥
  Eq⊥ = DecidableEquality→Eq DecEq⊥