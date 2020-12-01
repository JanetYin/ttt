module exampleExam where

-- BEGIN FIX

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

Eqn : ℕ → ℕ → Set
Eqn zero zero = ⊤
Eqn zero (suc b) = ⊥
Eqn (suc a) zero = ⊥
Eqn (suc a) (suc b) = Eqn a b

refln : (x : ℕ) → Eqn x x
refln zero = tt
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
idr zero    = tt
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

eq3 : ℕ → ℕ → ℕ → Bool
-- END FIX
eq3 = {!!}

-- BEGIN FIX
test-eq3-1 : Eq Bool (eq3 323 323 (321 + 2)) true
test-eq3-1 = refl
test-eq3-2 : Eq Bool (eq3 323 323 321) false
test-eq3-2 = refl
test-eq3-3 : Eq Bool (eq3 323 321 323) false
test-eq3-3 = refl
test-eq3-4 : Eq Bool (eq3 321 323 323) false
test-eq3-4 = refl
test-eq3-5 : Eq Bool (eq3 321 323 321) false
test-eq3-5 = refl

is666 : ℕ → Bool
-- END FIX
is666 = {!!}

-- BEGIN FIX
test-is666-1 : Eq Bool (is666 666) true
test-is666-1 = refl
test-is666-2 : Eq Bool (is666 667) false
test-is666-2 = refl
test-is666-3 : Eq Bool (is666 665) false
test-is666-3 = refl

weirdLogicalEquiv : (A B C : Set) → (A → (B → C × A)) ↔ (B × A → (C ⊎ ⊥))
-- END FIX
weirdLogicalEquiv = {!!}

-- BEGIN FIX
-- n1 and n2 should be such that n1 ℕ zero suc ≠ n2 ℕ zero suc
n1 n2 : (A : Set) → A → (A → A) → A
-- END FIX
n1 = {!!}
n2 = {!!}
 
-- BEGIN FIX
test-n1-n2 : ¬ Eqn (n1 ℕ zero suc) (n2 ℕ zero suc)
test-n1-n2 = λ x → x

some¬ : (A : Set) → ¬ ¬ ¬ ¬ A → ¬ ¬ (A ⊎ ⊥)
-- END FIX
some¬ = {!!}

-- BEGIN FIX
iso : (A B C : Set) → (A ⊎ B → C) ↔ ((A → C) × (B → C))
-- END FIX
iso = {!!}

-- BEGIN FIX
getX : (X : Set) → X ⊎ X ⊎ (⊤ → X) ⊎ (((A : Set) → A → A) → X) → X
-- END FIX
getX = {!!}

-- BEGIN FIX
lemma1 : ¬ ((n : ℕ) → Eqn (3 + n) (n + 1))
-- END FIX
lemma1 f = {!!}

-- BEGIN FIX
lemma2 : (n : ℕ) → ¬ Eqn (3 + n) (n + 1)
-- END FIX
lemma2 = {!!}

-- BEGIN FIX
eq : (x y z : ℕ) → Eqn (x + (y + y)) ((y + 0) + (y + x))
-- END FIX
eq = {!!}
