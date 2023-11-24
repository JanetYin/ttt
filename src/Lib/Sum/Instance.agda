{-# OPTIONS --safe #-}

module Lib.Sum.Instance where

open import Lib.Sum.Type

instance
  inlᵢ : ∀{i j}{A : Set i}{B : Set j} → ⦃ A ⦄ → A ⊎ B
  inlᵢ ⦃ x ⦄ = inl x

  inrᵢ : ∀{i j}{A : Set i}{B : Set j} → ⦃ B ⦄ → A ⊎ B
  inrᵢ ⦃ x ⦄ = inr x