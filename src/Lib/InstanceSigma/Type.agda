{-# OPTIONS --safe #-}
module Lib.InstanceSigma.Type where

open import Agda.Primitive
open import Lib.Sigma.Type

record ιΣ {ℓ κ}(A : Set ℓ)(B : ⦃ A ⦄ → Set κ) : Set (ℓ ⊔ κ) where
  constructor ι,
  field
    ⦃ fst ⦄ : A
    snd : B

open ιΣ public

ιΣ↔Σ : ∀{ℓ κ}{A : Set ℓ}{B : ⦃ A ⦄ → Set κ} → ιΣ A B ↔ Σ A λ a → B ⦃ a ⦄
fst ιΣ↔Σ (ι, ⦃ a ⦄ res) = a , res
fst (snd ιΣ↔Σ (a , res)) = a
snd (snd ιΣ↔Σ (a , res)) = res
