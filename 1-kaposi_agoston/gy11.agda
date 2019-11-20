module gy11 where

open import lib

Eqb : Bool → Bool → Set
Eqb = λ x y → if x then (if y then ⊤ else ⊥) else (if y then ⊥ else ⊤)

not : Bool → Bool
not = λ b → if b then false else true

ineq : (x : Bool) → ¬ Eqb x (not x)
ineq = {!!}

ID : (A : Set) → A → A
ID = {!!}

CONST : (A B : Set) → A → B → A
CONST = {!!}

comm× : (A B : Set) → (A × B) ↔ (B × A)
comm× = {!!}

module firstOrder
  (A B : Set)
  (P Q : A → Set)
  where

  ∀×-distr : ((x : A) → P x × Q x) ↔ ((x : A) → P x) × ((x : A) → Q x)
  ∀×-distr = {!!}

  ¬¬∀-nat : ¬ ¬ ((x : A) → P x) → (x : A) → ¬ ¬ (P x)
  ¬¬∀-nat = {!!}

  -- first order De Morgan

  ¬∀ : (Σ A λ x → ¬ P x) → ¬ ((x : A) → P x)
  ¬∀ = {!!}

-- We already know:
infixl 4 _+_
_+'_ : ℕ → ℕ → ℕ
_+'_ = λ x y → primrec y (λ _ z → suc z) x

eq' : ℕ → ℕ → Bool
eq' = λ x → primrec
                 (λ y → primrec true (λ _ _ → false) y)
                 (λ x' eq? y → primrec false (λ y' _ → eq? y') y)
                 x
_+_ : ℕ → ℕ → ℕ
_+_ = {!!}

eq : ℕ → ℕ → Bool
eq = {!!}

Eqn : ℕ → ℕ → Set
Eqn = {!!}

--indℕ : (P : ℕ → Set) → P zero → ((n : ℕ) → P n → P (suc n)) → (t : ℕ) → P t
--indℕ P u v zero = u
--indℕ P u v (suc t) = v t (indℕ P u v t)

-- use indℕ
refln' : (n : ℕ) → Eqn n n
refln' = {!!}

-- use pattern matching
refln : (n : ℕ) → Eqn n n
refln = {!!}

indℕ' : (P : ℕ → Set) → P zero → ((n : ℕ) → P n → P (suc n)) → (t : ℕ) → P t
indℕ' = {!!}

0lid : (n : ℕ) → Eqn (zero + n) n 
0lid = {!!}

zero≠suc : (x : ℕ) → ¬ Eqn zero (suc x)
zero≠suc = {!!}

suc-inj : (x y : ℕ) → Eqn (suc x) (suc y) → Eqn x y
suc-inj = {!!}

-- pattern matching
_*'_ : ℕ → ℕ → ℕ
_*'_ = {!!}

-- pattern matching
transport : (P : ℕ → Set)(x y : ℕ) → Eqn x y → P x → P y
transport = {!!}

sym : (x y : ℕ) → Eqn x y → Eqn y x
sym = {!!}

trans : (x y z : ℕ) → Eqn x y → Eqn y z → Eqn x z
trans = {!!}

-- pattern matching
cong : (f : ℕ → ℕ)(x y : ℕ) → Eqn x y → Eqn (f x) (f y)
cong f x y e = transport (λ y' → Eqn (f x) (f y')) x y e (refln (f x)) 

-- pattern matching
idl : (x : ℕ) → Eqn (zero + x) x
idl = {!!}

-- pattern matching
idr : (x : ℕ) → Eqn (x + zero) x
idr = {!!}

-- pattern matching
ass : (x y z : ℕ) → Eqn ((x + y) + z) (x + (y + z))
ass = {!!}

-- pattern matching
comm-lemm : (x y : ℕ) → Eqn (suc x + y) (x + suc y)
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


-- 1 + a + 2 * 0 = a + 1
exercise1 : (A : Set) → ⊤ ⊎ A ⊎ Bool × ⊥ ↔ A ⊎ ⊤
exercise1 = {!!}

Eqℕ×ℕ : ℕ × ℕ → ℕ × ℕ → Set
Eqℕ×ℕ = {!!}

iso→ : (Bool → ℕ) → ℕ × ℕ
iso→ = {!!}

iso← : (Bool → ℕ) ← ℕ × ℕ
iso← = {!!}
 
iso←→ : (w : ℕ × ℕ) → Eqℕ×ℕ (iso→ (iso← w)) w
iso←→ = {!!}

--

-- pattern matching
_*_ : ℕ → ℕ → ℕ
_*_ = {!!}

zerol* : (n : ℕ) → Eqn (zero * n) zero
zerol* = {!!}

zeror* : (n : ℕ) → Eqn (n * zero) zero
zeror* = {!!}

ass*   : (x y z : ℕ) → Eqn ((x * y) * z) (x * (y * z))
ass* = {!!}

comm*  : (x y : ℕ) → Eqn (x * y) (y * x)
comm* = {!!}

distr  : (x y z : ℕ) → Eqn (x * (y + z)) (x * y + x * z)
distr = λ x y z → {!!}

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

-- Hard:
ex1'' : (x y : ℕ) → Eqn ((x + (y + zero)) + x) (2 * x + y)
ex1'' x y = {!!}
