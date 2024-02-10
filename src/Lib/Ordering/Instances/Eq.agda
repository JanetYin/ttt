{-# OPTIONS --safe #-}

module Lib.Ordering.Instances.Eq where

open import Lib.Class.Eq
open import Lib.Ordering.Type
open import Lib.Dec
open import Lib.Ordering.Instances.DecidableEquality

instance
  EqOrdering : Eq Ordering
  EqOrdering = DecidableEquality→Eq DecEqOrdering