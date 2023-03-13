open import Agda.Builtin.Nat
  renaming (Nat to ℕ)
  public
open import Agda.Primitive
open import Agda.Builtin.Equality
  public
open import Agda.Builtin.Bool
  public
open import Agda.Builtin.Sigma
  public

infixr 4 _,_
infixr 2 _×_
infixr 1 _⊎_
infix 0 _↔_

if_then_else_ : ∀{i}{A : Set i}(t : Bool)(u v : A) → A
if true then u else v = u
--if_then_else_ true u v = u 
if false then u else v = v

{-
if true then 5 else 6 = 5
if false then 5 else 6 = 6
-}

-- Product types
record _×_ {i}{j}(A : Set i)(B : Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    fst : A
    snd : B
open _×_ public

-- Sum types
data _⊎_ {i}{j}(A : Set i)(B : Set j) : Set (i ⊔ j) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

--(A ⊎ B) → (A → C) → (B → C) → C
case : ∀ {i j k}{A : Set i}{B : Set j}{C : Set k}
         (aub : A ⊎ B)(f : A → C)(g : B → C) → C
case (inl a) f g = f a
case (inr b) f g = g b

-- Empty type
data ⊥ : Set where

exfalso : ∀{i}{A : Set i} → ⊥ → A
exfalso ()

-- Unit type
record ⊤ : Set where
  instance constructor tt
open ⊤ public

_↔_ : ∀{i j} → Set i → Set j → Set (i ⊔ j)
A ↔ B = (A → B) × (B → A)

¬_ : ∀{i} → Set i → Set i
¬ A = A → ⊥

infix 4 _≢_

_≢_ : ∀{i}{A : Set i}(x y : A) → Set i
x ≢ y = ¬ (x ≡ y)
