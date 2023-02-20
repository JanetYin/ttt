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

-- zero : ℕ
-- n : ℕ     then    suc n : ℕ
--                   n + 1

-- Recursive definitions can be given using pattern matching:

three-test : 3 ≡ suc (suc (suc zero)); three-test = refl

double : ℕ → ℕ
double zero    = zero
double (suc n) = suc (suc (double n))

double-test : double 10 ≡ 20; double-test = refl

-- Only terminating definitions are allowed.
-- Try to uncomment the following definition:
-- bad : ℕ → ℕ
-- bad zero    = zero
-- bad (suc n) = bad (suc (suc n))

-- f : ℕ → A
-- f (suc n) = ... -- here you can only use   f n

-- g (suc (suc n)) = ... -- here you can only use   f n  and  f (suc n)

half : ℕ → ℕ
half zero          = 0
half (suc (suc n)) = suc (half n)
half (suc zero)    = 0

half-test1 : half 10 ≡ 5
half-test1 = refl
half-test2 : half 11 ≡ 5
half-test2 = refl
half-test3 : half 12 ≡ 6
half-test3 = refl

-- _+_ and _*_ are also defined by recursion.

_+_ : ℕ → ℕ → ℕ
zero  + y = y
suc x + y = suc (x + y)
infixl 6 _+_

_+'_ : ℕ → ℕ → ℕ
x +' zero  = x
x +' suc y = suc (x + y)

_+''_ : ℕ → ℕ → ℕ
zero  +'' acc = acc
suc x +'' acc = x +'' suc acc

+-test1 : 3 + 5 ≡ 8
+-test1 = refl
+-test2 : 0 + 5 ≡ 5
+-test2 = refl
+-test3 : 5 + 0 ≡ 5
+-test3 = refl

_*_ : ℕ → ℕ → ℕ
zero  * y = zero
suc x * y = y + x * y
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
fib 0             = 1
fib 1             = 1
fib (suc (suc n)) = fib n + fib (suc n)

-- fib-helper n  returns  (fib n , fib (n+1))
fib-helper : ℕ → ℕ × ℕ
fib-helper zero    = 1 , 1
fib-helper (suc n) =
  let (x , y) = fib-helper n
  in y , x + y

fib' = λ n → fst (fib-helper n)

fib-test1 : fib' 6 ≡ 13
fib-test1 = refl
fib-test2 : fib' 3 ≡ 3
fib-test2 = refl

-- Exponentiation
_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ suc m = n * (n ^ m)
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
zero !  = 1
suc n ! = (suc n) * (n !)

!-test1 : 3 ! ≡ 6
!-test1 = refl
!-test2 : 1 ! ≡ 1
!-test2 = refl
!-test3 : 6 ! ≡ 720
!-test3 = refl

-- Negation of natural numbers
--  !!!  n - m = 0  when m > 0
_-_ : ℕ → ℕ → ℕ
zero - zero = 0
zero - suc m = 0
suc n - zero = suc n
suc n - suc m = n - m
infixl 6 _-_

-test1 : 3 - 2 ≡ 1
-test1 = refl
-test2 : 3 - 3 ≡ 0
-test2 = refl
-test3 : 3 - 4 ≡ 0
-test3 = refl

-- Comparison functions
_≥_ : ℕ → ℕ → Bool
zero ≥ zero = true
zero ≥ suc m = false
suc n ≥ zero = true
suc n ≥ suc m = n ≥ m

≥test1 : 3 ≥ 2 ≡ true
≥test1 = refl
≥test2 : 3 ≥ 3 ≡ true
≥test2 = refl
≥test3 : 3 ≥ 4 ≡ false
≥test3 = refl

_>_ : ℕ → ℕ → Bool
n > m = n ≥ suc m

>test1 : 3 > 2 ≡ true
>test1 = refl
>test2 : 3 > 3 ≡ false
>test2 = refl
>test3 : 3 > 4 ≡ false
>test3 = refl

_<_ : ℕ → ℕ → Bool
n < m = m > n

<test1 : 3 < 2 ≡ false
<test1 = refl
<test2 : 3 < 3 ≡ false
<test2 = refl
<test3 : 3 < 4 ≡ true
<test3 = refl

min : ℕ → ℕ → ℕ
min n m = if n < m then n else m

min-test1 : min 3 2 ≡ 2
min-test1 = refl
min-test2 : min 2 3 ≡ 2
min-test2 = refl
min-test3 : min 3 3 ≡ 3
min-test3 = refl

-- We can use the TERMINATING pragma to disable the termination checker.
gcd : ℕ → ℕ → ℕ
{-# TERMINATING #-}
gcd 0 n = n
gcd (suc n) 0 = suc n
gcd (suc n) (suc m) = if n < m then gcd (suc n) (m - n) else gcd (n - m) (suc m)

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
gcd-helper (suc fuel) zero m = m
gcd-helper (suc fuel) (suc n) zero = suc n
gcd-helper (suc fuel) (suc n) (suc m) = if n < m then gcd (suc n) (m - n) else gcd (n - m) (suc m)

gcd' : ℕ → ℕ → ℕ
gcd' m n = gcd-helper (suc (m + n)) m n

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
gcd'-test6 : gcd' 0 0 ≡ 0
gcd'-test6 = refl

not : Bool → Bool
not true = false
not false = true

even? : ℕ → Bool
even? zero = true
even? (suc n) = not (even? n)

-- even?-test1 : even? 3 ≡ false
-- even?-test1 = refl
-- even?-test2 : even? 200 ≡ true
-- even?-test2 = refl

eq : ℕ → ℕ → Bool
eq zero zero = true
eq zero (suc m) = false
eq (suc n) zero = false
eq (suc n) (suc m) = eq n m

-- rem n m = remainder of the division of n by (suc m)
rem : ℕ → ℕ → ℕ
rem zero    b = zero
rem (suc a) b =
  let rab = rem a b in
  if eq rab b then zero else suc rab

rem-test1 : rem 5 1 ≡ 1
rem-test1 = refl
rem-test2 : rem 11 2 ≡ 2
rem-test2 = refl

-- div n m = quotient of the division of n by (suc m)
div-rem : ℕ → ℕ → ℕ × ℕ
div-rem zero    b = zero , zero
div-rem (suc a) b =
  let qab , rab = div-rem a b in
  if eq rab b
  then (suc qab , zero)
  else (qab , suc rab)


div : ℕ → ℕ → ℕ
div a b = div-rem a b .fst

div-test1 : div 5 1 ≡ 2
div-test1 = refl
div-test2 : div 11 2 ≡ 3
div-test2 = refl
