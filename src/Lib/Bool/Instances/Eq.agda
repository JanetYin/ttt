{-# OPTIONS --safe #-}

module Lib.Bool.Instances.Eq where

open import Lib.Class.Eq

open import Lib.Dec

open import Lib.Bool.Type
open import Lib.Bool.Instances.DecidableEquality

instance
  EqBool : Eq Bool
  EqBool = DecidableEquality→Eq DecEqBool