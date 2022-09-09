module lib where

open import Agda.Primitive
open import Agda.Builtin.Nat renaming (Nat to ℕ) public
open import Agda.Builtin.Bool public
open import Agda.Builtin.Unit public

infixr 4 _,_
infixr 2 _×_
infixr 1 _⊎_
infixr 0 _↔_

record _×_ {i}{j}(A : Set i)(B : Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
open _×_ public

data _⊎_ {i}{j}(A : Set i)(B : Set j) : Set (i ⊔ j) where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

_↔_ : ∀{i j}(A : Set i)(B : Set j) → Set (i ⊔ j)
A ↔ B = (A → B) × (B → A)

data ⊥ : Set where

¬_ : ∀{i}(A : Set i) → Set i
¬ A = A → ⊥

-- open import Agda.Builtin.Sigma public
-- open import Agda.Builtin.Equality public
