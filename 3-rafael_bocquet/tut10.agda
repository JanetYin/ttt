module tut10 where
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
--          ≡ = \==
--          ∎ = \qed

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

Eqn-sym : (a b : ℕ) → Eqn a b → Eqn b a
Eqn-sym a b x = Eqn-transp (λ y → Eqn y a) a b x (Eqn-refl a)

Eqn-trans : (a b c : ℕ) → Eqn a b → Eqn b c → Eqn a c
Eqn-trans a b c p q = Eqn-transp (λ y → Eqn a y) b c q p

Eqn-cong : (x y : ℕ) → (f : ℕ → ℕ) → Eqn x y → Eqn (f x) (f y)
Eqn-cong x y f p = Eqn-transp (λ z → Eqn (f x) (f z)) x y p (Eqn-refl (f x))

---- Proofs about _+_

+-suc : (a b : ℕ) → Eqn (a + suc b) (suc (a + b))
+-suc zero b = Eqn-refl b
+-suc (suc a) b = +-suc a b

+-assoc : (a b c : ℕ) → Eqn ((a + b) + c) (a + (b + c))
+-assoc zero b c = Eqn-refl (b + c)
+-assoc (suc a) b c = +-assoc a b c

+-comm : (a b : ℕ) → Eqn (a + b) (b + a)
+-comm a zero = plusRightId a
+-comm a (suc b) = Eqn-trans (a + suc b) (suc (a + b)) (suc (b + a)) (+-suc a b) (+-comm a b)

-- More proofs about _+_

-- When using Eqn-trans to prove "Eqn a c", always write "Eqn-trans a b c ? ?"
-- first, typecheck (C-c C-l) and then fill the holes.
--
-- You can use Eqn-trans several times. Example:
-- If eq_a_b : Eqn a b, eq_b_c : Eqn b c, eq_c_d : Eqn c d, eq_d_e : Eqn d e, then
--       Eqn-trans a b e eq_a_b
--      (Eqn-trans b c e eq_b_c
--      (Eqn-trans c d e eq_c_d
--       eq_d_e))                  : Eqn a e

-- Use Eqn-trans, +-assoc, +-comm
2*-distr : (a b : ℕ) → Eqn (2 * (a + b)) (2 * a + 2 * b)
2*-distr a b = {!!}

-- Induction on a
2*-comm : (a : ℕ) → Eqn (2 * a) (a * 2)
2*-comm a = {!!}

-- Use Eqn-trans, 2*-distr, 2*-comm
*2-distr : (a b : ℕ) → Eqn ((a + b) * 2) (a * 2 + b * 2)
*2-distr = {!!}

-- Use Eqn-trans, +-assoc, +-comm, ???
ex1 : (x y : ℕ) → Eqn ((x + (y + zero)) + x) (2 * x + y)
ex1 = {!!}


---- Bonus : proofs about _*_ (without hints)

*+-distr : (a b c : ℕ) → Eqn (a * (b + c)) (a * b + a * c)
*+-distr a b c = {!!}

+*-distr : (a b c : ℕ) → Eqn ((a + b) * c) (a * c + b * c)
+*-distr a b c = {!!}

*-assoc : (a b c : ℕ) → Eqn ((a * b) * c) (a * (b * c))
*-assoc a b c = {!!}

*-comm : (a b : ℕ) → Eqn (a * b) (b * a)
*-comm a b = {!!}
