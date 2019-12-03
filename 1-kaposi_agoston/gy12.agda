module gy12 where

open import lib

Eqn : ℕ → ℕ → Set
Eqn zero zero = ⊤
Eqn zero (suc y) = ⊥
Eqn (suc x) zero = ⊥
Eqn (suc x) (suc y) = Eqn x y

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

refln : (n : ℕ) → Eqn n n
refln = λ n → indℕ (λ n → Eqn n n) tt (λ _ e → e) n

-- pattern matching
transport : (P : ℕ → Set)(x y : ℕ) → Eqn x y → P x → P y
transport P zero zero e px = px
transport P (suc x) zero e px = exfalso e
transport P zero (suc y) e px = exfalso e
transport P (suc x) (suc y) e px = transport (λ n → P (suc n)) x y e px

-- use transport to define sym
sym : (x y : ℕ) → Eqn x y → Eqn y x
sym = λ x y e → transport (λ n → Eqn n x) x y e (refln x) 

-- use transport to define trans
trans : (x y z : ℕ) → Eqn x y → Eqn y z → Eqn x z
trans = λ x y z exy eyz → transport (λ n → Eqn x n) y z eyz exy 

extratransitivity : (x y z : ℕ) → Eqn x y → Eqn x z → Eqn y z
extratransitivity x y z = transport (λ n → Eqn n z) x y 
  
-- pattern matching
idl : (x : ℕ) → Eqn (zero + x) x
idl zero = tt
idl (suc x) = idl x

-- pattern matching
idr : (x : ℕ) → Eqn (x + zero) x
idr = {!!}

-- pattern matching
ass : (x y z : ℕ) → Eqn ((x + y) + z) (x + (y + z))
ass = {!!}

cong : (f : ℕ → ℕ)(x y : ℕ) → Eqn x y → Eqn (f x) (f y)
cong = {!!}

-- pattern matching
comm-lemm : (x y : ℕ) → Eqn (suc (x + y)) (x + suc y)
comm-lemm = {!!}

-- pattern matching
comm : (x y : ℕ) → Eqn (x + y) (y + x)
comm = {!!}

-- define primrec with indℕ!
primrec' : (A : Set)(u : A)(v : ℕ → A → A)(t : ℕ) → A
primrec' = {!!}

-- define if_then_else with indBool
if'_then_else : (A : Set)(t : Bool)(u v : A) → A
if'_then_else = {!!}

--ind⊎ : (A : Set)(B : Set)(P : A ⊎ B → Set) → ((a : A) → P (inj₁ a)) → ((b : B) → P (inj₂ b)) → (t : A ⊎ B) → P t
--ind⊎ P u v (inj₁ t) = u t
--ind⊎ P u v (inj₂ t) = v t
-- define case with ind⊎!
case' : (A : Set)(B : Set)(C : Set)(t : A ⊎ B)(u : A → C)(v : B → C) → C
case' = {!!}

infixl 4 _+_
infixl 5 _*_

_*_ : ℕ → ℕ → ℕ
zero * y = zero
suc x * y = y + x * y

ex1 : (x y : ℕ) → Eqn (x + zero + y) (y + x)
ex1 = {!!}

ex2 : (x y : ℕ) → Eqn ((x + (y + zero)) + x) (2 * x + y)
ex2 = {!!}

zerol* : (n : ℕ) → Eqn (zero * n) zero
zerol* = {!!}

zeror* : (n : ℕ) → Eqn (n * zero) zero
zeror* = {!!}
--- EDDIG JUTOTTUNK EL ---
idl* : (n : ℕ) → Eqn (1 * n) n
idl* = {!!}

idr* : (n : ℕ) → Eqn (n * 1) n
idr* = {!!}

distr  : (x y z : ℕ) → Eqn (x * (y + z)) (x * y + x * z)
distr = {!!}

comm*-lemma : (x y : ℕ) → Eqn (y + y * x) (y * suc x)
comm*-lemma = {!!}

comm* : (x y : ℕ) → Eqn (x * y) (y * x)
comm* = {!!}

distrl : (x y z : ℕ) → Eqn ((x + y) * z) (x * z + y * z)
distrl = {!!}

ass* : (x y z : ℕ) → Eqn ((x * y) * z) (x * (y * z))
ass* = {!!}
-- less than or equal

_≤_ : ℕ → ℕ → Set
_≤_ = {!!}

ex : 3 ≤ 100
ex = {!!}

refl≤ : (x : ℕ) → x ≤ x
refl≤ = {!!}

trans≤ : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
trans≤ = {!!}

≤dec : (x y : ℕ) → x ≤ y ⊎ y ≤ x
≤dec = {!!}

