open import lib

-- Define a function which triples a given ℕ (without using _+_ or _*_):
triple : ℕ → ℕ
triple n = {!!}

-- Define the power operator (_^_). Here you can use _+_ or _*_.

_^_ : ℕ → ℕ → ℕ
n ^ m = {!!}

^test1 : 0 ^ 5 ≡ 0
^test1 = refl
^test2 : 100 ^ 0 ≡ 1
^test2 = refl
^test3 : 3 ^ 4 ≡ 81
^test3 = refl

-- Generalize the Fibonacci series for any given starting values. This means a₀ and a₁ must be given, and then for all n: aₙ₊₂ = aₙ + aₙ₊₁.
fibgen : ℕ → ℕ → (ℕ → ℕ)
fibgen a0 a1 = {!!}

fibgentest1 : fibgen 5 6 0 ≡ 5
fibgentest1 = refl
fibgentest2 : fibgen 5 6 1 ≡ 6
fibgentest2 = refl
fibgentest3 : fibgen 5 6 2 ≡ (5 + 6)
fibgentest3 = refl

-- Try to define rem and div without {-# TERMINATING #-} ! You may need some helper functions.
-- rem a b = remainder of the division of a by (suc b).
--  /!\ Since division by zero is not possible, the second argument is shifted by 1 (see the examples).
rem : ℕ → ℕ → ℕ
rem a b = {!!} --#termination checking failed: if (a < b) then a else (rem (a - b) b)

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
