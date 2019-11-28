module tut11 where
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
-- C-u C-u C-c C-, : Type of the hole fully normalised
-- C-u C-u C-c C-. : Type of the hole and expression, fully normalised
-- C-u C-c C-, : Type of the hole not normalised at all
-- C-u C-c C-. : Type of the hole and expression, not normalised at all
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

infix 3 _≤_
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

Eqn-sym : (a b : ℕ) → Eqn a b → Eqn b a
Eqn-sym a b x = Eqn-transp (λ y → Eqn y a) a b x (Eqn-refl a)

Eqn-trans : (a b c : ℕ) → Eqn a b → Eqn b c → Eqn a c
Eqn-trans a b c p q = Eqn-transp (λ y → Eqn a y) b c q p

Eqn-cong : (x y : ℕ) → (f : ℕ → ℕ) → Eqn x y → Eqn (f x) (f y)
Eqn-cong x y f p = Eqn-transp (λ z → Eqn (f x) (f z)) x y p (Eqn-refl (f x))

---- Proofs about _+_

+-idr : (x : ℕ) → Eqn (x + zero) x
+-idr zero = tt
+-idr (suc x) = +-idr x

+-idl : (x : ℕ) → Eqn (zero + x) x
+-idl x = Eqn-refl x

+-suc : (a b : ℕ) → Eqn (a + suc b) (suc (a + b))
+-suc zero b = Eqn-refl b
+-suc (suc a) b = +-suc a b

+-assoc : (a b c : ℕ) → Eqn ((a + b) + c) (a + (b + c))
+-assoc zero b c = Eqn-refl (b + c)
+-assoc (suc a) b c = +-assoc a b c

+-comm : (a b : ℕ) → Eqn (a + b) (b + a)
+-comm a zero = +-idr a
+-comm a (suc b) = Eqn-trans (a + suc b) (suc (a + b)) (suc (b + a)) (+-suc a b) (+-comm a b)

---- proofs about _*_

*-nulll : (a : ℕ) → Eqn (0 * a) 0
*-nulll = {!!}

*-nullr : (a : ℕ) → Eqn (a * 0) 0
*-nullr = {!!}

*-idl : (a : ℕ) → Eqn (1 * a) a
*-idl = {!!}

*-idr : (a : ℕ) → Eqn (a * 1) a
*-idr = {!!}

*+-distr : (a b c : ℕ) → Eqn (a * (b + c)) (a * b + a * c)
*+-distr a b c = {!!}

+*-distr : (a b c : ℕ) → Eqn ((a + b) * c) (a * c + b * c)
+*-distr a b c = {!!}

*-assoc : (a b c : ℕ) → Eqn ((a * b) * c) (a * (b * c))
*-assoc a b c = {!!}

*-comm : (a b : ℕ) → Eqn (a * b) (b * a)
*-comm a b = {!!}

--- properties of ≤

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

≤-antisym : (x y : ℕ) → x ≤ y → y ≤ x → Eqn x y
≤-antisym = {!!}

≤-dec : (x y : ℕ) → x < y ⊎ Eqn x y ⊎ y < x
≤-dec = {!!}

≤-equiv : (x y : ℕ) → x ≤ y ↔ Σ ℕ λ k → Eqn (k + x) y
≤-equiv = {!!}

+≤ : (x y a : ℕ) → a + x ≤ a + y ↔ x ≤ y
+≤ = {!!}

1+*≤ : (x y a : ℕ) → suc a * x ≤ suc a * y ↔ x ≤ y
1+*≤ = {!!}

¬*≤ : ¬ ((x y a : ℕ) → a * x ≤ a * y ↔ x ≤ y)
¬*≤ = {!!}
