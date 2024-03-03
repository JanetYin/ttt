{-# OPTIONS --safe #-}

module Lib.Nat.Instances.Ord where

open import Lib.Nat.Type
open import Lib.Nat.Properties
open import Lib.Nat.Instances.Eq

open import Lib.Ordering.Type
open import Lib.Class.Eq
open import Lib.Class.Ord

open import Lib.Sigma.Type

open import Lib.Equality

open import Lib.Sum.Type
open import Lib.Sum.Base

open import Lib.Unit.Type

open import Lib.Maybe.Type
open import Lib.Maybe.Base

instance
  Ordℕ : Ord ℕ
  Ord.eq Ordℕ = Eqℕ
  Ord.compare Ordℕ zero zero = EQ
  Ord.compare Ordℕ zero (suc y) = LT
  Ord.compare Ordℕ (suc x) zero = GT
  Ord.compare Ordℕ (suc x) (suc y) = compare x y
  Ord.flippable Ordℕ {zero} {zero} = (λ ()) , (λ ())
  Ord.flippable Ordℕ {zero} {suc y} = (λ x → refl) , (λ x → refl)
  Ord.flippable Ordℕ {suc x} {zero} = (λ ()) , (λ ())
  Ord.flippable Ordℕ {suc x} {suc y} = flippable {x = x} {y}
  Ord.equality Ordℕ {zero} = refl
  Ord.equality Ordℕ {suc x} = equality {x = x}
  Ord.consistencyWithEq Ordℕ {zero} {zero} = λ _ → refl
  Ord.consistencyWithEq Ordℕ {zero} {suc y} = λ ()
  Ord.consistencyWithEq Ordℕ {suc x} {zero} = λ ()
  Ord.consistencyWithEq Ordℕ {suc x} {suc y} e with x ≡ᵗ y in eq1
  ... | just p , t , r = Ord.consistencyWithEq Ordℕ {x} {y} (cast (trans r (sym (cong (λ a → fst (snd a)) eq1))) tt)