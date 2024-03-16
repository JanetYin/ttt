{-# OPTIONS --safe #-}

module Lib.Sigma.Type where

open import Agda.Primitive using (_⊔_)
open import Agda.Builtin.Sigma public

infix 2 Σ-syntax

Σ-syntax : ∀{a b}(A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = [ x ∶ A ] × B

infixr 2 _×_
_×_ : ∀{i j}(A : Set i)(B : Set j) → Set (i ⊔ j)
A × B = Σ A (λ _ → B)

infix 0 _↔_
_↔_ : ∀{i j} → Set i → Set j → Set (i ⊔ j)
A ↔ B = (A → B) × (B → A)
