open import Agda.Builtin.Nat
  renaming (Nat to ℕ)
  public
open Agda.Primitive
  renaming (Set to Type)
  public

infixr 4 _,_
infixr 2 _×_
infixr 1 _⊎_

-- Booleans
data 𝔹 : Set where
  true false : 𝔹

if_then_else_ : ∀{i}{A : Type i}(t : 𝔹)(u v : A) → A
if true  then u else v = u
if false then u else v = v

-- Product types
record _×_ {i}{j}(A : Type i)(B : Type j) : Type (i ⊔ j) where
  constructor _,_
  field
    π₁ : A
    π₂ : B
open _×_ public

-- Sum types
data _⊎_ {i}{j}(A : Type i)(B : Type j) : Type (i ⊔ j) where
  ι₁ : A → A ⊎ B
  ι₂ : B → A ⊎ B

case : ∀ {i j k}{A : Type i}{B : Type j}{C : Type k}
         (t : A ⊎ B)(u : A → C)(v : B → C) → C
case (ι₁ t) u v = u t
case (ι₂ t) u v = v t

-- Empty type
data ⊥ : Set where

exfalso : ∀{i}{A : Set i} → ⊥ → A
exfalso ()

-- Unit type
record ⊤ : Set where
  constructor tt
open ⊤ public
