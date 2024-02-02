{-# OPTIONS --safe #-}

module Lib.Nat.Instances.Eq where

open import Lib.Class.Eq
open import Lib.Nat
open import Lib.Sigma
open import Lib.Maybe
open import Lib.Equality
open import Lib.Empty.Type
open import Lib.Unit.Type

instance
  Eqℕ : Eq ℕ
  (Eqℕ Eq.≡ᵗ zero) zero = just refl , ⊤ , refl
  (Eqℕ Eq.≡ᵗ zero) (suc b) = nothing , ⊥ , refl
  (Eqℕ Eq.≡ᵗ suc a) zero = nothing , ⊥ , refl
  (Eqℕ Eq.≡ᵗ suc a) (suc b) with (Eqℕ Eq.≡ᵗ a) b
  ... | just p , x = just (cong suc p) , x
  ... | nothing , x = nothing , x
