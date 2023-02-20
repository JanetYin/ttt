module gy10 where

open import lib

Eqb : Bool → Bool → Set
Eqb = λ x y → if x then (if y then ⊤ else ⊥) else (if y then ⊥ else ⊤)

not : Bool → Bool
not = λ b → if b then false else true

-- sigma:
-- Dependent pairs: Σ A B
-- if A is a type and B : A → Set, then Σ A B is a type
-- intoduction:
-- if u : A and v : B u, then u , v : Σ A B
-- elimination:
-- if t : Σ A B then proj₁ t : A
-- if t : Σ A B then proj₂ t : B (proj₁ t)
-- computation:
-- proj₁ (u , v) = u
-- proj₂ (u , v) = v
-- uniqueness:
-- (λ x → t x) = t
ex : Σ Bool (λ b → Eqb (not b) false)
ex = {!!}

Σ⊎-distr : (A : Set)(P Q : A → Set) → (Σ A λ x → P x ⊎ Q x) ↔ Σ A P ⊎ Σ A Q
Σ⊎-distr = {!!}

-- note: A × B can be defined as Σ A (λ _ → B)

currying : (A C : Set) → (P : A → Set) → (Σ A P → C) ↔ ((x : A) → (P x → C))
currying = {!!}

-- indBool : (P : Bool → Set) → P true → P false → (t : Bool) → P t
-- indBool P u v true = u
-- indBool P u v false = v
helper : (A B : Set) → (b : Bool) → (if b then A else B → A ⊎ B)
helper = {!!}

-- (Σ A P → C) ↔ ((x : A) → (P x → C))
ex4 : (A B : Set) → Σ Bool (λ b → if b then A else B) ↔ (A ⊎ B) 
ex4 = {!!}

--

true=true : Eqb true true
true=true = {!!}

¬true=false : ¬ Eqb true false
¬true=false = {!!}

lem1 : (x : Bool) → Eqb true x → ¬ Eqb x false
lem1 = {!!}

Eqb-refl : (x : Bool) → Eqb x x
Eqb-refl = {!!}

ID : (A : Set) → A → A
ID = {!!}

CONST : (A B : Set) → A → B → A
CONST = {!!}

comm× : (A B : Set) → (A × B) ↔ (B × A)
comm× = {!!}

module firstOrder
  (A B : Set)
  (P Q : A → Set)
  (R : A → B → Set)
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
_+_ : ℕ → ℕ → ℕ
_+_ = λ x y → primrec y (λ _ z → suc z) x
eq : ℕ → ℕ → Bool
eq = λ x → primrec
                 (λ y → primrec true (λ _ _ → false) y)
                 (λ x' eq? y → primrec false (λ y' _ → eq? y') y)
                 x
Eqn : ℕ → ℕ → Set
Eqn = λ x y → Eqb (eq x y) true

--indℕ : (P : ℕ → Set) → P zero → ((n : ℕ) → P n → P (suc n)) → (t : ℕ) → P t
--indℕ P u v zero = u
--indℕ P u v (suc t) = v t (indℕ P u v t)

-- use indℕ
refl-= : (n : ℕ) → Eqn n n
refl-= = {!!}

0lid : (n : ℕ) → Eqn (zero + n) n 
0lid = {!!}

0rid : (n : ℕ) → Eqn (n + zero) n 
0rid = {!!}

0rid' : (n : ℕ) → Eqn n (n + zero) 
0rid' = {!!}

lem : (a b : ℕ) → Eqn (suc (a + b)) (a + suc b)
lem = {!!}


zero≠suc : (x : ℕ) → ¬ Eqn zero (suc x)
zero≠suc = {!!}

suc-inj : (x y : ℕ) → Eqn (suc x) (suc y) → Eqn x y
suc-inj = {!!}

-- pattern matching
_+'_ : ℕ → ℕ → ℕ
_+'_ = {!!}
--_+_ : ℕ → ℕ → ℕ
--_+_ = λ x y → primrec y (λ x' z → suc z) x

_*'_ : ℕ → ℕ → ℕ
_*'_ = {!!}

-- (pattern matching)
Eqn-transp : (x y : ℕ)(P : ℕ → Set) → Eqn x y → P x → P y
Eqn-transp = {!!}

Eqn-symm : (x y : ℕ) → Eqn x y → Eqn y x
Eqn-symm = {!!}

Eqn-trans : (x y z : ℕ) → Eqn x y → Eqn y z → Eqn x z
Eqn-trans = {!!}

-- Hard
-- Segitseg: indukcios felteves és lem 
comm+ : (a b : ℕ) → Eqn (a + b) (b + a)
comm+ = {!!}

-- define primrec with indℕ!
primrec' : (A : Set)(u : A)(v : ℕ → A → A)(t : ℕ) → A
primrec' = {!!}

-- define if_then_else with indBool
if'_then_else : (A : Set)(t : Bool)(u v : A) → A
if'_then_else = {!!}

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
