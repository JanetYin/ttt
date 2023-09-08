{-# OPTIONS --safe --guardedness #-}

module Lib.Containers.Stream.Bisimulation where

open import Lib.Containers.Stream.Type
open import Lib.Equality

infixr 5 _∷S_
infix 4 _≈S_
record _≈S_ {a}{A : Set a}(xs ys : Stream A) : Set a where
  constructor _∷S_
  coinductive
  field
    head-≡ : head xs ≡ head ys
    tail-≈ : tail xs ≈S tail ys
  
open _≈S_ public