{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude

module Circle where

data S¹ : Type where
  base : S¹
  loop : base ≡ base