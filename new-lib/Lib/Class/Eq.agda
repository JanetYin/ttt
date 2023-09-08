{-# OPTIONS --safe #-}

module Lib.Class.Eq where

open import Agda.Primitive
open import Lib.Empty.Base

record Eq {i} (A : Set i) : Set (lsuc i) where
  inductive
  field
    _≡ᵗ_ : A → A → Σ Set (λ A → A ≡ ⊤ ⊎ A ≡ ⊥)
    
  _≡ⁱ_ : A → A → Set
  a ≡ⁱ b = fst (a ≡ᵗ b)

  _≢ᵗ_ : A → A → Set
  a ≢ᵗ b = ?
  infix 4 _≡ᵗ_ _≡ⁱ_ _≢ᵗ_

open Eq {{...}} public

open import Lib.Bool.Type
open import Lib.Bool.Base

record Eqᵇ {i} (A : Set i) : Set i where
  inductive
  field
    _≡ᵇ_ : A → A → Bool
  _≢ᵇ_ : A → A → Bool
  a ≢ᵇ b = not (a ≡ᵇ b)
  infix 4 _≡ᵇ_ _≢ᵇ_

open Eqᵇ {{...}} public