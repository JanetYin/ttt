module tut9 where
open import lib

-- Emacs key bindings (C = Ctrl, M = Alt):
-- C-x C-f : create or open a file
-- C-x C-s : save a file
-- C-x C-c : close Emacs
-- M-w : Copy
-- C-y : Paste
--
-- Agda-mode key bindings:
-- C-c C-l : Typecheck
-- C-c C-n : Evaluate
-- C-c C-, : Check the type of a hole
-- C-c C-. : Check the type of a hole, and the type of the expresion in the hole
-- C-c C-SPACE : Fill a hole
-- C-c C-r : Try to automatically fill a hole
-- C-c C-c : Case split.
-- C-c C-a : Try to fill a hole automatically
--
-- Symbols: λ = \lambda
--          × = \times
--          → = \r
--          ₁ = \_1
--          ₂ = \_2
--          ⊎ = \u+
--          ≤ = \le
--          ↔ = \<->
--          ⊤ = \top
--          ⊥ = \bot
--          ¬ = \neg

infixl 4 _+_
infixl 5 _*_

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc n + m = suc (n + m)

_*_ : ℕ → ℕ → ℕ
zero * m = zero
suc n * m = m + (n * m)

Eqn : ℕ → ℕ → Set
Eqn zero    zero = ⊤
Eqn zero    (suc y) = ⊥
Eqn (suc x) zero = ⊥
Eqn (suc x) (suc y) = Eqn x y

---

Eqn-transp : (P : ℕ → Set) (x y : ℕ) (p : Eqn x y) → P x → P y
Eqn-transp P zero zero p a = a
Eqn-transp P zero (suc y) p a = exfalso p
Eqn-transp P (suc x) zero p a = exfalso p
Eqn-transp P (suc x) (suc y) p a = Eqn-transp (λ z → P (suc z)) x y p a

Eqn-refl : (n : ℕ) → Eqn n n
Eqn-refl zero = tt
Eqn-refl (suc n) = Eqn-refl n

plusRightId : (x : ℕ) → Eqn (x + zero) x
plusRightId zero = tt
plusRightId (suc x) = plusRightId x

plusLeftId : (x : ℕ) → Eqn (zero + x) x
plusLeftId x = Eqn-refl x

-- Define Eqn-sym (symmetry of Eqn) using Eqn-transp
Eqn-sym : (a b : ℕ) → Eqn a b → Eqn b a
Eqn-sym = {!!}

-- Define Eqn-trans (transitivity of Eqn) using Eqn-transp
Eqn-trans : (a b c : ℕ) → Eqn a b → Eqn b c → Eqn a c
Eqn-trans = {!!}

-- There is not natural number x that is equal to both 1 and 2
-- Hint: use Eqn-sym and Eqn-transp to prove (Eqn x 1 × Eqn x 2) → Eqn 1 2
ex0 : (x : ℕ) → ¬ (Eqn x 1 × Eqn x 2)
ex0 = {!!}

-- Define Eqn-cong (congruence of Eqn) using Eqn-transp
Eqn-cong : (x y : ℕ) → (f : ℕ → ℕ) → Eqn x y → Eqn (f x) (f y)
Eqn-cong x y f p = {!!}

-- Use Eqn-cong to prove:
ex1 : (x y : ℕ) → Eqn x y → Eqn (2 * x * x + 3 * x + 5) (2 * y * y + 3 * y + 5)
ex1 = {!!}

---- Proofs about _+_
---- We have already proven (0 + x = x) and (x + 0 = x) in tut7.agda
---- We now do more complicated proofs about _+_

-- Define +-suc by induction on a
+-suc : (a b : ℕ) → Eqn (a + suc b) (suc (a + b))
+-suc a b = {!!}

-- Define +-assoc by induction on a
+-assoc : (a b c : ℕ) → Eqn ((a + b) + c) (a + (b + c))
+-assoc a b c = {!!}

-- Define +-comm by induction on either a or b
-- Hint: Eqn-trans, plusRightId and +-suc may be needed
+-comm : (a b : ℕ) → Eqn (a + b) (b + a)
+-comm a b = {!!}

---- Proofs about _≤_
_≤_ : ℕ → ℕ → Set
zero  ≤ y     = ⊤
suc x ≤ zero  = ⊥
suc x ≤ suc y = x ≤ y

_<_ : ℕ → ℕ → Set
x < y = suc x ≤ y

≤-refl : (x : ℕ) → x ≤ x
≤-refl = {!!}

≤-trans : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
≤-trans = {!!}

ex4 : (x y : ℕ) → x ≤ y ↔ (x < y ⊎ Eqn x y)
ex4 x y = {!!}

-- Comparison function for natural numbers
≤-dec : (x y : ℕ) → x < y ⊎ Eqn x y ⊎ y < x
≤-dec x y = {!!}

ex3 : (x y : ℕ) → ¬ Eqn x y → x < y ⊎ y < x
ex3 = {!!}

---- Proofs about _*_ (without hints)

*-assoc : (a b c : ℕ) → Eqn ((a * b) * c) (a * (b * c))
*-assoc a b c = {!!}

*-comm : (a b : ℕ) → Eqn (a * b) (b * a)
*-comm a b = {!!}
