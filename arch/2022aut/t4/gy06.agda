module t4.gy06 where
open import lib hiding (_+_; _*_; _-_; _<_)

-- List of unicode symbols:
--    →       \to
--            \rightarrow
--    ℕ       \bN           'b'lackboard 'N', there is also \bZ for ℤ, etc
--    λ       \Gl           'G'reek 'l', there is also \GG for Γ, etc
--            \lambda
--    ×       \times
--    ⊎       \u+
--    ⊤       \top
--    ⊥       \bot
--    ↔       \lr
--    ₁       \_1
--    ₐ       \_a
--    ¹       \^1

---------------------------------------------------------
-- natural numbers
---------------------------------------------------------

-- data ℕ : Type where
--   zero : ℕ       -- nullary constructor
--   suc  : ℕ → ℕ   -- unary constructor
--                     suc n  =  n+1

three : ℕ
three = suc (suc (suc zero))

-- elimination of ℕ  ~~~  recursion / induction on natural numbers
--  pattern matching

-- later: define "recursor" and "eliminator" as functions.

double : ℕ → ℕ
double zero    = zero
double (suc x) = suc (suc (double x))

double-test1 : double 2 ≡ 4
double-test1 = refl
double-test2 : double 0 ≡ 0
double-test2 = refl
double-test3 : double 10 ≡ 20
double-test3 = refl

-- Non-terminating functions:
-- bad : ℕ → ℕ
-- bad zero    = zero
-- bad (suc x) = suc (bad (suc x))

half : ℕ → ℕ
half = {!!}

-- half-test1 : half 10 ≡ 5
-- half-test1 = refl
-- half-test2 : half 11 ≡ 5
-- half-test2 = refl
-- half-test3 : half 12 ≡ 6
-- half-test3 = refl

_+_ : ℕ → ℕ → ℕ
_+_ = {!!}
infixl 6 _+_

-- +-test1 : 3 + 5 ≡ 8
-- +-test1 = refl
-- +-test2 : 0 + 5 ≡ 5
-- +-test2 = refl
-- +-test3 : 5 + 0 ≡ 5
-- +-test3 = refl

_*_ : ℕ → ℕ → ℕ
_*_ = {!!}
infixl 7 _*_

-- *-test1 : 3 * 4 ≡ 12
-- *-test1 = refl
-- *-test2 : 3 * 1 ≡ 3
-- *-test2 = refl
-- *-test3 : 3 * 0 ≡ 0
-- *-test3 = refl
-- *-test4 : 0 * 10 ≡ 0
-- *-test4 = refl

_^_ : ℕ → ℕ → ℕ
_^_ = {!!}
infixl 8 _^_

-- ^-test1 : 3 ^ 4 ≡ 81
-- ^-test1 = refl
-- ^-test2 : 3 ^ 0 ≡ 1
-- ^-test2 = refl
-- ^-test3 : 0 ^ 3 ≡ 0
-- ^-test3 = refl
-- ^-test4 : 1 ^ 3 ≡ 1
-- ^-test4 = refl
-- ^-test5 : 0 ^ 0 ≡ 1
-- ^-test5 = refl

_! : ℕ → ℕ
_! = {!!}

-- !-test1 : 3 ! ≡ 6
-- !-test1 = refl
-- !-test2 : 1 ! ≡ 1
-- !-test2 = refl
-- !-test3 : 6 ! ≡ 720
-- !-test3 = refl

-- Negation of natural numbers
--  /!\  n - m = 0  when m > 0

_-_ : ℕ → ℕ → ℕ
_-_ = {!!}
infixl 6 _-_

-- -test1 : 3 - 2 ≡ 1
-- -test1 = refl
-- -test2 : 3 - 3 ≡ 0
-- -test2 = refl
-- -test3 : 3 - 4 ≡ 0
-- -test3 = refl

-- Comparison functions
_≥_ : ℕ → ℕ → Bool
_≥_ = {!!}

-- ≥test1 : 3 ≥ 2 ≡ true
-- ≥test1 = refl
-- ≥test2 : 3 ≥ 3 ≡ true
-- ≥test2 = refl
-- ≥test3 : 3 ≥ 4 ≡ false
-- ≥test3 = refl

_>_ : ℕ → ℕ → Bool
_>_ = {!!}

-- >test1 : 3 > 2 ≡ true
-- >test1 = refl
-- >test2 : 3 > 3 ≡ false
-- >test2 = refl
-- >test3 : 3 > 4 ≡ false
-- >test3 = refl

_<_ : ℕ → ℕ → Bool
_<_ = {!!}

-- <test1 : 3 < 2 ≡ false
-- <test1 = refl
-- <test2 : 3 < 3 ≡ false
-- <test2 = refl
-- <test3 : 3 < 4 ≡ true
-- <test3 = refl

min : ℕ → ℕ → ℕ
min = {!!}

-- min-test1 : min 3 2 ≡ 2
-- min-test1 = refl
-- min-test2 : min 2 3 ≡ 2
-- min-test2 = refl
-- min-test3 : min 3 3 ≡ 3
-- min-test3 = refl

-- We can use the TERMINATING pragma to disable the termination checker.
gcd : ℕ → ℕ → ℕ
{-# TERMINATING #-}
gcd n m = {!!}

-- gcd-test1 : gcd 6 9 ≡ 3
-- gcd-test1 = refl
-- gcd-test2 : gcd 100 150 ≡ 50
-- gcd-test2 = refl
-- gcd-test3 : gcd 17 19 ≡ 1
-- gcd-test3 = refl
-- gcd-test4 : gcd 12 24 ≡ 12
-- gcd-test4 = refl
-- gcd-test5 : gcd 19 17 ≡ 1
-- gcd-test5 = refl

-- Use the same definition as for `gcd`, but with recursion on the first parameter.
--   gcd-helper fuel n m  should be equal to  gcd n m  when fuel is large enough.
gcd-helper : ℕ → ℕ → ℕ → ℕ
gcd-helper zero       n m = 42
gcd-helper (suc fuel) n m = {!!}

gcd' : ℕ → ℕ → ℕ
gcd' n m = gcd-helper (m + n + 1) n m

-- gcd'-test1 : gcd' 6 9 ≡ 3
-- gcd'-test1 = refl
-- gcd'-test2 : gcd' 100 150 ≡ 50
-- gcd'-test2 = refl
-- gcd'-test3 : gcd' 17 19 ≡ 1
-- gcd'-test3 = refl
-- gcd'-test4 : gcd' 12 24 ≡ 12
-- gcd'-test4 = refl
-- gcd'-test5 : gcd' 19 17 ≡ 1
-- gcd'-test5 = refl

not : Bool → Bool
not true = false
not false = true

even? : ℕ → Bool
even? = {!!}

-- even?-test1 : even? 3 ≡ false
-- even?-test1 = refl
-- even?-test2 : even? 200 ≡ true
-- even?-test2 = refl

fib : ℕ → ℕ
fib = {!!}

-- fib-test1 : fib 6 ≡ 13
-- fib-test1 = refl
-- fib-test2 : fib 3 ≡ 3
-- fib-test2 = refl

-- divrem2 a should be a pair (q , r) where q and r are the quotient and remainder of the division of a by 2.
--  The remainder r is encoded as a boolean: 0 corresponds to false and 1 corresponds to true.
divrem2 : ℕ → ℕ × Bool
divrem2 = {!!}

-- divrem2-test1 : divrem2 5  ≡ 2 , true
-- divrem2-test1 = refl
-- divrem2-test2 : divrem2 10 ≡ 5 , false
-- divrem2-test2 = refl

-- Try to define rem and div without {-# TERMINATING #-} ! You may need some helper functions.
-- rem a b = remainder of the division of a by (suc b).
--  /!\ Since division by zero is not possible, the second argument is shifted by 1 (see the examples).

rem : ℕ → ℕ → ℕ
rem a b = {!!}

-- rem-test1 : rem 5 1 ≡ 1
-- rem-test1 = refl
-- rem-test2 : rem 11 2 ≡ 2
-- rem-test2 = refl

-- div a b = quotient of the division of a by (suc b)

div : ℕ → ℕ → ℕ
div a b = {!!}

-- div-test1 : div 5 1 ≡ 2
-- div-test1 = refl
-- div-test2 : div 11 2 ≡ 3
-- div-test2 = refl
