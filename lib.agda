module lib where

open import Agda.Primitive

infixr 4 _,_
infixr 2 _×_
infixr 1 _⊎_
infixr 0 _↔_
infixr 0 _←_

data Bool : Set where
  true false : Bool

if_then_else_ : ∀{i}{A : Set i}(t : Bool)(u v : A) → A
if true then u else v = u
if false then u else v = v

record _×_ {i}{j}(A : Set i)(B : Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
open _×_ public

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

primrec : ∀{i}{A : Set i}(u : A)(v : ℕ → A → A)(t : ℕ) → A
primrec u v zero = u
primrec u v (suc t) = v t (primrec u v t)

postulate
   X Y Z : Set

data _⊎_ {i}{j}(A : Set i)(B : Set j) : Set (i ⊔ j) where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

case : ∀ {i j k}{A : Set i}{B : Set j}{C : Set k}
       (t : A ⊎ B)(u : A → C)(v : B → C) → C
case (inj₁ t) u v = u t
case (inj₂ t) u v = v t

_↔_ : ∀{i j}(A : Set i)(B : Set j) → Set (i ⊔ j)
A ↔ B = (A → B) × (B → A)

data ⊥ : Set where

exfalso : ∀{i}{A : Set i} → ⊥ → A
exfalso ()

record ⊤ : Set where
  constructor tt
open ⊤ public

¬_ : ∀{i}(A : Set i) → Set i
¬ A = A → ⊥

_←_ : ∀{i j}(A : Set i)(B : Set j) → Set (i ⊔ j)
A ← B = B → A

indℕ : ∀{i}(P : ℕ → Set i) → P zero → ((n : ℕ) → P n → P (suc n)) → (t : ℕ) → P t
indBool : ∀{i}(P : Bool → Set i) → P true → P false → (t : Bool) → P t
ind⊎ : ∀{i j k}{A : Set i}{B : Set j}(P : A ⊎ B → Set k) → ((a : A) → P (inj₁ a)) → ((b : B) → P (inj₂ b)) → (t : A ⊎ B) → P t

indℕ P u v zero = u
indℕ P u v (suc t) = v t (indℕ P u v t)
indBool P u v true = u
indBool P u v false = v
ind⊎ P u v (inj₁ t) = u t
ind⊎ P u v (inj₂ t) = v t

record Σ {i}{j}(A : Set i)(B : A → Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
open Σ public

data Eq {i}(A : Set i)(a : A) : A → Set where
  refl : Eq A a a
