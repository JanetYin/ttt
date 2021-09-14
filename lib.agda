module lib where

open import Agda.Primitive

infixr 4 _,_
infixr 2 _×_
infixr 1 _⊎_
infixr 0 _↔_

data 𝟚 : Set where
  tt ff : 𝟚

if_then_else_ : ∀{i}{A : Set i}(t : 𝟚)(u v : A) → A
if tt then u else v = u
if ff then u else v = v

record _×_ {i}{j}(A : Set i)(B : Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    π₁ : A
    π₂ : B
open _×_ public

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

rec : ∀{i}{A : Set i}(u : A)(v : A → A)(t : ℕ) → A
rec u v zero = u
rec u v (suc t) = v (rec u v t)

data _⊎_ {i}{j}(A : Set i)(B : Set j) : Set (i ⊔ j) where
  ι₁ : A → A ⊎ B
  ι₂ : B → A ⊎ B

case : ∀ {i j k}{A : Set i}{B : Set j}{C : Set k}
       (t : A ⊎ B)(u : A → C)(v : B → C) → C
case (ι₁ t) u v = u t
case (ι₂ t) u v = v t

_↔_ : ∀{i j}(A : Set i)(B : Set j) → Set (i ⊔ j)
A ↔ B = (A → B) × (B → A)

data ⊥ : Set where

exfalso : ∀{i}{A : Set i} → ⊥ → A
exfalso ()

record ⊤ : Set where
  constructor triv
open ⊤ public

¬_ : ∀{i}(A : Set i) → Set i
¬ A = A → ⊥

indℕ : ∀{i}(P : ℕ → Set i) → P zero → ((n : ℕ) → P n → P (suc n)) → (t : ℕ) → P t
ind𝟚 : ∀{i}(P : 𝟚 → Set i) → P tt → P ff → (t : 𝟚) → P t
ind⊎ : ∀{i j k}{A : Set i}{B : Set j}(P : A ⊎ B → Set k) → ((a : A) → P (ι₁ a)) → ((b : B) → P (ι₂ b)) → (t : A ⊎ B) → P t

indℕ P u v zero = u
indℕ P u v (suc t) = v t (indℕ P u v t)
ind𝟚 P u v tt = u
ind𝟚 P u v ff = v
ind⊎ P u v (ι₁ t) = u t
ind⊎ P u v (ι₂ t) = v t

record Σ {i}{j}(A : Set i)(B : A → Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    π₁ : A
    π₂ : B π₁
open Σ public

data Eq {i}(A : Set i)(a : A) : A → Set i where
  refl : Eq A a a
