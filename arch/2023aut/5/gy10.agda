open import Lib

---------------------------------------------------------
-- equational reasoning
------------------------------------------------------

p4 : (x y : ℕ) → ((x + (y + zero)) + x) ≡ (2 * x + y)
p4 = {!!}

p3 : (a b : ℕ) → a + a + b + a * 0 ≡ 2 * a + b
p3 = {!!}

p2 : (a b c : ℕ) → c * (b + 1 + a) ≡ a * c + b * c + c
p2 = {!!}

[m+n]^2=m^2+2mn+n^2 : (m n : ℕ) → (m + n) * (m + n) ≡ m * m + 2 * m * n + n * n
[m+n]^2=m^2+2mn+n^2 = {!!}

{-
infixr 8 _^'_
_^'_ : ℕ → ℕ → ℕ
x ^' zero  = 1
x ^' suc n = x * x ^' n

infixr 8 _^_
_^_ : (x y : ℕ) → .⦃ y + x ≢ℕ 0 ⦄ → ℕ
x ^ zero = 1
x ^ suc zero = x
x ^ suc (suc y) = x * (x ^ suc y)

-- A vesszős definíciót érdemes használni.
-- A simáról nehéz állításokat bizonyítani.
-}

p1 : (a b : ℕ) → (a + b) ^' 2 ≡ a ^' 2 + 2 * a * b + b ^' 2
p1 a b = {!!}

0^ : (n : ℕ) → 0 ^' (suc n) ≡ 0
0^ = {!!}

^0 : (a : ℕ) → a ^' 0 ≡ 1
^0 = {!!}

1^ : (n : ℕ) → 1 ^' n ≡ 1
1^ = {!!}

^1 : (a : ℕ) → a ^' 1 ≡ a
^1 = {!!}

^+ : (a m n : ℕ) → a ^' (m + n) ≡ a ^' m * a ^' n
^+ = {!!}

*^ : (a b n : ℕ) → (a * b) ^' n ≡ a ^' n * b ^' n
*^ = {!!}

^* : (a m n : ℕ) → a ^' (m * n) ≡ (a ^' m) ^' n
^* = {!!}
