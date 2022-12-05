module exampleExam where

-- Fill in the holes!

-- marks:
-- 0-4  1
-- 5-6  2
-- 7-8  3
-- 9-9  4
-- >9   5

open import Agda.Primitive

infixr 4 _,_
infixr 2 _×_
infixr 1 _⊎_
infixr 0 _↔_
infixr 0 _←_

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

_←_ : ∀{i j}(A : Set i)(B : Set j) → Set (i ⊔ j)
A ← B = B → A

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

data Eq {i}(A : Set i)(a : A) : A → Set where
  refl : Eq A a a

Eqn : ℕ → ℕ → Set
Eqn zero zero = ⊤
Eqn zero (suc b) = ⊥
Eqn (suc a) zero = ⊥
Eqn (suc a) (suc b) = Eqn a b

refln : (x : ℕ) → Eqn x x
refln zero = triv
refln (suc x) = refln x

transport : (P : ℕ → Set)(x y : ℕ) → Eqn x y → P x → P y
transport P zero    zero    e u = u
transport P (suc x) zero    e u = exfalso e
transport P zero    (suc y) e u = exfalso e
transport P (suc x) (suc y) e u = transport (λ x → P (suc x)) x y e u

sym : (x y : ℕ) → Eqn x y → Eqn y x
sym x y e = transport (λ z → Eqn z x) x y e (refln x)

trans : (x y z : ℕ) → Eqn x y → Eqn y z → Eqn x z
trans x y z e e' = transport (λ q → Eqn x q) y z e' e

cong : (f : ℕ → ℕ)(x y : ℕ) → Eqn x y → Eqn (f x) (f y)
cong f x y e = transport (λ y → Eqn (f x) (f y)) x y e (refln (f x))

_+_ : ℕ → ℕ → ℕ
zero + b = b
suc a + b = suc (a + b)

idl : (x : ℕ) → Eqn (zero + x) x
idl x = refln x

idr : (x : ℕ) → Eqn (x + zero) x
idr zero    = triv
idr (suc x) = idr x

ass : (x y z : ℕ) → Eqn ((x + y) + z) (x + (y + z))
ass zero    y z = refln (y + z)
ass (suc x) y z = ass x y z

comm-lemm : (x y : ℕ) → Eqn (suc x + y) (x + suc y)
comm-lemm zero    y = refln y
comm-lemm (suc x) y = comm-lemm x y

comm : (x y : ℕ) → Eqn (x + y) (y + x)
comm zero y    = sym (y + zero) y (idr y)
comm (suc x) y = trans (suc (x + y)) (suc (y + x)) (y + suc x) (comm x y) (comm-lemm y x)

eq3 : ℕ → ℕ → ℕ → 𝟚
eq3 = {!!}

test-eq3-1 : Eq 𝟚 (eq3 323 323 (321 + 2)) tt
test-eq3-1 = refl
test-eq3-2 : Eq 𝟚 (eq3 323 323 321) ff
test-eq3-2 = refl
test-eq3-3 : Eq 𝟚 (eq3 323 321 323) ff
test-eq3-3 = refl
test-eq3-4 : Eq 𝟚 (eq3 321 323 323) ff
test-eq3-4 = refl
test-eq3-5 : Eq 𝟚 (eq3 321 323 321) ff
test-eq3-5 = refl

is666 : ℕ → 𝟚
is666 = {!!}

test-is666-1 : Eq 𝟚 (is666 666) tt
test-is666-1 = refl
test-is666-2 : Eq 𝟚 (is666 667) ff
test-is666-2 = refl
test-is666-3 : Eq 𝟚 (is666 665) ff
test-is666-3 = refl

weirdLogicalEquiv : (A B C : Set) → (A → (B → C × A)) ↔ (B × A → (C ⊎ ⊥))
weirdLogicalEquiv = {!!}

-- n1 and n2 should be such that n1 ℕ zero suc ≠ n2 ℕ zero suc
n1 n2 : (A : Set) → A → (A → A) → A
n1 = {!!}
n2 = {!!}
 
test-n1-n2 : ¬ Eqn (n1 ℕ zero suc) (n2 ℕ zero suc)
test-n1-n2 = λ x → x

some¬ : (A : Set) → ¬ ¬ ¬ ¬ A → ¬ ¬ (A ⊎ ⊥)
some¬ = {!!}

iso : (A B C : Set) → (A ⊎ B → C) ↔ ((A → C) × (B → C))
iso = {!!}

getX : (X : Set) → X ⊎ X ⊎ (⊤ → X) ⊎ (((A : Set) → A → A) → X) → X
getX = {!!}

lemma1 : ¬ ((n : ℕ) → Eqn (3 + n) (n + 1))
lemma1 = {!!}

lemma2 : (n : ℕ) → ¬ Eqn (3 + n) (n + 1)
lemma2 = {!!}

eq : (x y z : ℕ) → Eqn (x + (y + y)) ((y + 0) + (y + x))
eq = {!!}
