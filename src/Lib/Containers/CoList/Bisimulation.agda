{-# OPTIONS --safe --guardedness #-}

module Lib.Containers.CoList.Bisimulation where

open import Lib.Containers.CoList.Type
open import Lib.Equality
open import Lib.Unit
open import Lib.Empty
open import Lib.Sum
open import Lib.Sigma
open import Lib.Level

infix 4 _≈L_ _≈L′_
record _≈L_ {a} {A : Set a} (xs ys : CoList A) : Set a

_≈L′_ : ∀{a}{A : Set a}(xs ys : CoList′ A) → Set a
_≈L′_ {a} (inl _) (inl _) = Lift a ⊤
_≈L′_ {a} (inl _) (inr _) = Lift a ⊥
_≈L′_ {a} (inr _) (inl _) = Lift a ⊥
(x ∷∞ xs) ≈L′ (y ∷∞ ys) = x ≡ y × xs ≈L ys

record _≈L_ {a} {A} xs ys where
  coinductive
  field prove : headTail xs ≈L′ headTail ys

open _≈L_ public