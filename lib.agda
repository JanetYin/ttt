module lib where

infix  4 _,_
infixr 2 _×_
infixr 1 _⊎_

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

ind : {A : Set}(u : A)(v : ℕ → A → A)(t : ℕ) → A
ind u v zero = u
ind u v (suc t) = v t (ind u v t)

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B
