module tut.t1.tut+++ where

open import lib
open import tut.t1.gy07

-- ha n < m, akkor legyen a Bool false
dec_by_ : ℕ → ℕ → (ℕ × Bool)
dec n by m = {!!}

-- ha m = 0, n mod m = 0 , false 
-- nem kell feltétlenül használni az előzőt
-- (ez a feladat nem trivi)
_mod_ : ℕ → ℕ → (ℕ × Bool)
n mod m = {!!}

-- ha a mod megvan, ez már csak a jutalom :)
isPrime : ℕ → Bool
isPrime n = {!!}
                                                
-- wikipédia szerint ez legit
e1 : ({A B : Set} → ¬ (A × B) → (¬ A ⊎ ¬ B)) →  
  {A : Set} → ¬ A ⊎ ¬ ¬ A ↔ ⊤
e1 dm = {!!}
      , {!!}

-- listákkal felvértezve, próbáljatok Eratoszthenészi szitát implementálni

boolFunction : (f : Bool → Bool)(x : Bool) → Eqb (f (f (f x))) (f x)
boolFunction f = {!!}

Eqℕ-sym : (a b : ℕ) → Eqℕ a b → Eqℕ b a
Eqℕ-sym = {!!}

lem3 : (x : ℕ) → Eqℕ x (suc (suc zero)) → Eqℕ (suc (suc (suc zero))) (suc x)
lem3 = {!!}

_^_ : Set → ℕ → Set
A ^ n = rec ⊤ (A ×_ ) n

Vec : (A : Set)(n : ℕ) → Set
Vec A n = A ^ n

-- add meg indukcióval!
foldr : ∀{A}{i}{B : Set i}{n} → B → (A → B → B) → Vec A n → B
foldr = {!!}
