module 2021aut.t2.gy11.advanced-properties-solved where
open import lib
open import 2021aut.t2.gy10.basic-properties-solved

-- use indℕ, trans, suc+
comm : (a b : ℕ) → Eqℕ (a + b) (b + a)
comm = λ a b → indℕ
  (λ a → Eqℕ (a + b) (b + a))
  (sym (b + 0) b (idr b))
  (λ n e → trans (suc n + b) (suc b + n) (b + suc n) e (suc+ b n))
  a

_*_ : ℕ → ℕ → ℕ
_*_ = λ a b → rec 0 (_+_ b) a
infixl 7 _*_

-- laws for muliplication

-- use indℕ
idl* : (a : ℕ) → Eqℕ (1 * a) a
idl* = indℕ (λ a → Eqℕ (1 * a) a) (reflℕ 0) (λ _ e → e)

-- use indℕ
idr* : (a : ℕ) → Eqℕ (a * 1) a
idr* = indℕ (λ a → Eqℕ (a * 1) a) (reflℕ 0) (λ _ e → e)

-- no need for indℕ
nulll : (a : ℕ) → Eqℕ (0 * a) 0
nulll = λ _ → reflℕ 0

-- use indℕ
nullr : (a : ℕ) → Eqℕ (a * 0) 0
nullr = indℕ (λ a → Eqℕ (a * 0) 0) (reflℕ 0) (λ _ e → e)

-- use indℕ, trans, cong, sym, ass
distr : (a b c : ℕ) → Eqℕ ((a + b) * c) (a * c + b * c)
distr = λ a b c → indℕ
  (λ a → Eqℕ ((a + b) * c) (a * c + b * c))
  (reflℕ (b * c))
  (λ n e → trans
    ((suc n + b) * c)
    (c + (n * c + b * c))
    (suc n * c + b * c)
    (cong (_+_ c) ((n + b) * c) (n * c + b * c) e)
    (sym (suc n * c + b * c) (c + (n * c + b * c)) (ass c (n * c) (b * c))))
  a

-- use indℕ, trans, distr, cong
ass* : (a b c : ℕ) → Eqℕ ((a * b) * c) (a * (b * c))
ass* = λ a b c → indℕ
  (λ a → Eqℕ ((a * b) * c) (a * (b * c)))
  triv
  (λ n e → trans
    (suc n * b * c)
    (b * c + (n * b) * c)
    (suc n * (b * c))
    (distr b (n * b) c)
    (cong (_+_ (b * c)) ((n * b) * c) (n * (b * c)) e))
  a

-- use indℕ, trans, sym, ass, cong, comm
suc* : (a b : ℕ) → Eqℕ (a + a * b) (a * suc b)
suc* = λ a b → indℕ
  (λ a → Eqℕ (a + a * b) (a * suc b))
  (reflℕ 0)
  (λ n e → trans
    (suc n + suc n * b)
    (suc b + (n + n * b))
    (suc n * suc b)
    (trans
      (n + (b + n * b))
      ((n + b) + n * b)
      (b + (n + n * b))
      (sym (n + b + n * b) (n + (b + n * b)) (ass n b (n * b)))
      (trans
        ((n + b) + n * b)
        ((b + n) + n * b)
        (b + (n + n * b))
        (cong (_+ (n * b)) (n + b) (b + n) (comm n b))
        (ass b n (n * b))))
    (cong (_+_ (suc b)) (n + n * b) (n * suc b) e))
  a

-- use indℕ, nullr, trans, suc*
comm* : (a b : ℕ) → Eqℕ (a * b) (b * a)
comm* = λ a b → indℕ
  (λ a → Eqℕ (a * b) (b * a))
  (sym (b * zero) zero (nullr b))
  (λ n e → trans
    (suc n * b)
    (b + b * n)
    (b * suc n)
    (cong (_+_ b) (n * b) (b * n) e)
    (suc* b n))
  a

-- left distributivity: use comm* and distr
distl : (a b c : ℕ) → Eqℕ (a * (b + c)) (a * b + a * c)
distl = {!!}

-------------------------------------------------
-- building on the above
-------------------------------------------------

p4 : (x y : ℕ) → Eqℕ ((x + (y + zero)) + x) (2 * x + y)
p4 = {!!}

p3 : (a b : ℕ) → Eqℕ (a + a + b + a * 0) (2 * a + b)
p3 = {!!}

p2 : (a b c : ℕ) → Eqℕ (c * (b + 1 + a)) (a * c + b * c + c)
p2 = {!!}


