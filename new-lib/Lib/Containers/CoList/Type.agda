{-# OPTIONS --safe --guardedness #-}

module Lib.Containers.CoList.Type where

open import Lib.Unit
open import Lib.Sum
open import Lib.Sigma

record CoList {a}(A : Set a) : Set a

CoList′ : ∀{a}(A : Set a) → Set a
CoList′ A = ⊤ ⊎ (A × CoList A)

record CoList A where
  coinductive
  constructor mkCoList
  field
    headTail : CoList′ A
  
  infixr 5 _∷∞_
  pattern []∞ = inl tt
  pattern _∷∞_ x xs = inr (x , xs)

  head : ⊤ ⊎ A
  head with headTail
  ... | []∞ = inl tt
  ... | x ∷∞ _ = inr x

  tail : ⊤ ⊎ CoList A
  tail with headTail
  ... | []∞ = inl tt
  ... | _ ∷∞ xs = inr xs

open CoList public