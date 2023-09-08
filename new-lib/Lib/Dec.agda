{-# OPTIONS --safe #-}

module Lib.Dec where

open import Lib.Bool.Type
open import Lib.Equality
open import Lib.Sum.Type
open import Lib.Empty.Base

{-
infix 2 _because_
record Dec {p} (P : Set p) : Set p where
  constructor _because_
  field
    does  : Bool
    proof : Reflects P does
  
  pattern yes p = record { does = true ; proof = ofʸ p }
  pattern no ¬p = record { does = false ; proof = ofⁿ ¬p }

open Dec public
-}

Dec : ∀{i}(A : Set i) → Set i
Dec A = A ⊎ ¬ A

pattern no x = inr x
pattern yes x = inl x

Decidable : ∀{i j}{A : Set i} → (A → Set j) → Set _
Decidable P = ∀ x → Dec (P x)

Decidable₂ : ∀{i j k}{A : Set i}{B : Set j} → (P : A → B → Set k) → Set _
Decidable₂ _∼_ = ∀ x y → Dec (x ∼ y) 

DecidableEquality : ∀{i}(A : Set i) → Set _
DecidableEquality A = Decidable₂ {A = A} _≡_