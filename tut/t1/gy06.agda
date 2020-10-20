module tut.t1.gy06 where

open import lib
open import Agda.Primitive

-- Mi a típusa az alábbiaknak?
-- ℕ × Bool
-- Set
-- Bool → Set
-- Set₁ ⊎ Set₂
-- Set → Bool

-- universe polymorphism
opid : ∀{i}{A : Set i} → A → A
opid x = x

-- kumulativitás ugyan nincs, de ezt lehet
record ↑ {i} (A : Set i) : Set (lsuc i) where
  constructor ↑[_]↑ 
  field
    ↓[_]↓ : A
open ↑ public

-- Mi a típusa ennek?
-- ∀{i}{A : Set i} → A → A

-- elsőrendű logika
e1 : {A : Set} {P Q : A → Set} → ((a : A) → P a × Q a)  → ((a : A) → P a) × ((a : A) → Q a) 
e1 t = {!!}

e2 : {A : Set} {P Q : A → Set} → ((a : A) → P a) × ((a : A) → Q a) → ((a : A) → P a × Q a)
e2 t a = {!!}

e3 : {A : Set}{P Q : A → Set} → ((a : A) → P a → Q a) → ((a : A) → P a) → (a : A) → Q a
e3 t u a = {!!}

_^_ : (A : Set)(n : ℕ) → Set
A ^ n = rec ⊤ (λ u → A × u) n

Vec' : (A : Set)(n : ℕ) → Set
Vec' A n = A ^ n

-- listák
head : {!!}
head = {!!}

tail : {!!}
tail = {!!}

-- hogyan adjuk meg vektorra a rekurziót?
foldr' : ∀{n}{A B : Set} → (A → B → B) → A → Vec' A n → B 
foldr' f u ls = {!!}
