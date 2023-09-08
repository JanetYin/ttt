{-# OPTIONS --safe #-}

module Lib.Sigma.Type where

open import Agda.Primitive using (_⊔_)
open import Agda.Builtin.Sigma public

infixr 2 _×_
_×_ : ∀{i j}(A : Set i)(B : Set j) → Set (i ⊔ j)
A × B = Σ A (λ _ → B)

infix 0 _↔_
_↔_ : ∀{i j} → Set i → Set j → Set (i ⊔ j)
A ↔ B = (A → B) × (B → A)