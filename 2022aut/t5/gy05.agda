module t5.gy05 where
open import lib hiding (_+_; _*_; _<_; _-_)

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

--- Definitions by recursion on natural numbers.

-- The type of (unary) natural numbers is defined as a data type in Agda:
-- data ℕ : Type where
--   zero : ℕ
--   suc  : ℕ → ℕ

-- Recursive definitions can be given using pattern matching:

double : ℕ → ℕ
double zero    = zero
double (suc n) = suc (suc (double n))

double-test : double 10 ≡ 20; double-test = refl

-- Only terminating definitions are allowed.
-- Try to uncomment the following definition:
-- bad : ℕ → ℕ
-- bad zero    = zero
-- bad (suc n) = bad (n + n)

half : ℕ → ℕ
half = {!!}

half-test1 : half 10 ≡ 5
half-test1 = refl
half-test2 : half 11 ≡ 5
half-test2 = refl
half-test3 : half 12 ≡ 6
half-test3 = refl

-- _+_ and _*_ are also defined by recursion.

_+_ : ℕ → ℕ → ℕ
_+_ = {!!}
infixl 6 _+_

+-test1 : 3 + 5 ≡ 8
+-test1 = refl
+-test2 : 0 + 5 ≡ 5
+-test2 = refl
+-test3 : 5 + 0 ≡ 5
+-test3 = refl

_*_ : ℕ → ℕ → ℕ
_*_ = {!!}
infixl 7 _*_

*-test1 : 3 * 4 ≡ 12
*-test1 = refl
*-test2 : 3 * 1 ≡ 3
*-test2 = refl
*-test3 : 3 * 0 ≡ 0
*-test3 = refl
*-test4 : 0 * 10 ≡ 0
*-test4 = refl

-- The fibonacci sequence (fib 0 = fib 1 = 1; fib n = fib (n-1) + fib (n-2) when n ≥ 2)
fib : ℕ → ℕ
fib = {!!}

fib-test1 : fib 6 ≡ 13
fib-test1 = refl
fib-test2 : fib 3 ≡ 3
fib-test2 = refl

-- Exponentiation
_^_ : ℕ → ℕ → ℕ
_^_ = {!!}
infixl 8 _^_

^-test1 : 3 ^ 4 ≡ 81
^-test1 = refl
^-test2 : 3 ^ 0 ≡ 1
^-test2 = refl
^-test3 : 0 ^ 3 ≡ 0
^-test3 = refl
^-test4 : 1 ^ 3 ≡ 1
^-test4 = refl
^-test5 : 0 ^ 0 ≡ 1
^-test5 = refl

-- The factorial function
_! : ℕ → ℕ
_! = {!!}

!-test1 : 3 ! ≡ 6
!-test1 = refl
!-test2 : 1 ! ≡ 1
!-test2 = refl
!-test3 : 6 ! ≡ 720
!-test3 = refl

-- Negation of natural numbers
--  !!!  n - m = 0  when m > 0
_-_ : ℕ → ℕ → ℕ
_-_ = {!!}
infixl 6 _-_

-test1 : 3 - 2 ≡ 1
-test1 = refl
-test2 : 3 - 3 ≡ 0
-test2 = refl
-test3 : 3 - 4 ≡ 0
-test3 = refl

-- Comparison functions
_≥_ : ℕ → ℕ → Bool
_≥_ = {!!}

≥test1 : 3 ≥ 2 ≡ true
≥test1 = refl
≥test2 : 3 ≥ 3 ≡ true
≥test2 = refl
≥test3 : 3 ≥ 4 ≡ false
≥test3 = refl

_>_ : ℕ → ℕ → Bool
_>_ = {!!}

>test1 : 3 > 2 ≡ true
>test1 = refl
>test2 : 3 > 3 ≡ false
>test2 = refl
>test3 : 3 > 4 ≡ false
>test3 = refl

_<_ : ℕ → ℕ → Bool
_<_ = {!!}

<test1 : 3 < 2 ≡ false
<test1 = refl
<test2 : 3 < 3 ≡ false
<test2 = refl
<test3 : 3 < 4 ≡ true
<test3 = refl

min : ℕ → ℕ → ℕ
min = {!!}

min-test1 : min 3 2 ≡ 2
min-test1 = refl
min-test2 : min 2 3 ≡ 2
min-test2 = refl
min-test3 : min 3 3 ≡ 3
min-test3 = refl

-- We can use the TERMINATING pragma to disable the termination checker.
gcd : ℕ → ℕ → ℕ
{-# TERMINATING #-}
gcd m n = {!!}

gcd-test1 : gcd 6 9 ≡ 3
gcd-test1 = refl
gcd-test2 : gcd 100 150 ≡ 50
gcd-test2 = refl
gcd-test3 : gcd 17 19 ≡ 1
gcd-test3 = refl
gcd-test4 : gcd 12 24 ≡ 12
gcd-test4 = refl
gcd-test5 : gcd 19 17 ≡ 1
gcd-test5 = refl

-- Use the same definition as for `gcd`, but with recursion on the first parameter.
--   gcd-helper fuel n m  should be equal to  gcd n m  when fuel is large enough.
gcd-helper : ℕ → ℕ → ℕ → ℕ
gcd-helper zero       m n = 42
gcd-helper (suc fuel) m n = {!!}

gcd' : ℕ → ℕ → ℕ
gcd' m n = gcd-helper (m + n) m n

gcd'-test1 : gcd' 6 9 ≡ 3
gcd'-test1 = refl
gcd'-test2 : gcd' 100 150 ≡ 50
gcd'-test2 = refl
gcd'-test3 : gcd' 17 19 ≡ 1
gcd'-test3 = refl
gcd'-test4 : gcd' 12 24 ≡ 12
gcd'-test4 = refl
gcd'-test5 : gcd' 19 17 ≡ 1
gcd'-test5 = refl

not : Bool → Bool
not true = false
not false = true

even? : ℕ → Bool
even? = {!!}

even?-test1 : even? 3 ≡ true
even?-test1 = refl
even?-test2 : even? 200 ≡ false
even?-test2 = refl

-- rem n m = remainder of the division of n by (suc m)
rem : ℕ → ℕ → ℕ
rem a b = {!!}

rem-test1 : rem 5 1 ≡ 1
rem-test1 = refl
rem-test2 : rem 11 2 ≡ 2
rem-test2 = refl

-- div n m = quotient of the division of n by (suc m)
div : ℕ → ℕ → ℕ
div a b = {!!}

div-test1 : div 5 1 ≡ 2
div-test1 = refl
div-test2 : div 11 2 ≡ 3
div-test2 = refl
