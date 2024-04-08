{-# OPTIONS --safe --guardedness #-}

module Lib.Containers.CoList.Bisimilarity where

open import Lib.Containers.CoList.Type
open import Lib.Containers.CoList.PatternSynonym
open import Lib.Equality.Type
open import Lib.Unit.Type
open import Lib.Empty.Type
open import Lib.Maybe.Type
open import Lib.Sigma.Type
open import Lib.Level

infix 4 _≈L_ _≈L′_
record _≈L_ {a} {A : Set a} (xs ys : CoList A) : Set a

_≈L′_ : ∀{a}{A : Set a}(xs ys : Maybe (A × CoList A)) → Set a
_≈L′_ {a} nothing nothing = Lift a ⊤
_≈L′_ {a} nothing (just _) = Lift a ⊥
_≈L′_ {a} (just _) nothing = Lift a ⊥
(x ∷∞ xs) ≈L′ (y ∷∞ ys) = x ≡ y × xs ≈L ys

record _≈L_ {a} {A} xs ys where
  coinductive
  field prove : uncons xs ≈L′ uncons ys

open _≈L_ public
