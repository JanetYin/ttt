module lib where

infix  4 _,_
infixr 2 _×_
infixr 1 _⊎_
infixr 0 _↔_

data Bool : Set where
  true false : Bool

if_then_else_ : {A : Set}(t : Bool)(u v : A) → A
if true then u else v = u
if false then u else v = v

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
open _×_

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

primrec : {A : Set}(u : A)(v : ℕ → A → A)(t : ℕ) → A
primrec u v zero = u
primrec u v (suc t) = v t (primrec u v t)

postulate
   X Y Z : Set

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

_↔_ : (A B : Set) → Set
A ↔ B = (A → B) × (B → A)

data ⊥ : Set where

exfalso : {A : Set} → ⊥ → A
exfalso ()

record ⊤ : Set where
  constructor rr

¬_ : (A : Set) → Set
¬ A = A → ⊥
