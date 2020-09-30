{-# OPTIONS --no-pattern-match #-}

module tut.t2.gy02 where

open import lib

-- termeszetes szamok

-- ℕ ≡ \bN
three : ℕ 
three = suc (suc (suc zero))

seventyseven : ℕ
seventyseven = 77

-- teszteld oket!

plus3 : ℕ → ℕ
plus3 = λ x → suc (suc (suc x))

plus3' : ℕ → ℕ
plus3' = λ x → rec 3 (λ y → suc y ) x 

-- plus3' 0       = 3
-- plus3' (suc n) = v (plus3' n)
-- rec u v (suc t) = v (rec u v t)
-- ha x = suc n : v (plus3' n) 

times2 : ℕ → ℕ
times2 = λ x → rec 0 (λ y → suc (suc y)) x

-- ha x = 0,     akkor              2 * 0       = 0
-- ha x = suc n, akkor tfh y = 2*n, 2 * (suc n) = 2 * n + 2 = y + 2

_*3+2 : ℕ → ℕ
_*3+2 = rec 2 plus3
--_*3+2 = λ x → rec 2 (λ y → plus3 y) x

-- ha x = 0,     akkor                0       * 3 + 2 = 2
-- ha x = suc n, akkor tfh y = n*3+2, (suc n) * 3 + 2 = n * 3 + 2 + 3 = y + 3 

_+_ : ℕ → (ℕ → ℕ)
_+_ = λ x → λ y → rec x (λ z → suc z) y

-- ha y = 0     akkor                x + 0     = x
-- ha y = suc n akkor tfh z = x + n, x + suc n = x + n + 1 = z + 1 = suc z

_*_ : ℕ → (ℕ → ℕ)
_*_ = λ x y → rec 0 (λ z → z + x) y

_^_ : ℕ → (ℕ → ℕ)
_^_ = λ x y → rec 1 (λ z → z * x) y

-- mi a kulonbseg az alabbi ket fuggveny kozott?

idℕ : ℕ → ℕ
idℕ = λ x → x

idℕ' : ℕ → ℕ
idℕ' = λ x → rec zero suc x

-- sokkal lassabban typecheckel, ha idℕ helyett idℕ' van:

testid : Eq ℕ (idℕ 10000000) 10000000
testid = refl

-- ez konnyu:

is0 : ℕ → Bool
is0 = λ x → rec true (λ _ → false) x

-- ha x = 0     : true
-- ha x = suc n : false

not : Bool → Bool
not = λ x → if x then false else true

isEven : ℕ → Bool
isEven = λ x → rec true (λ y → not y) x

-- isEven (n + 1 ) = not (isEven n)

isnot0 : ℕ → Bool
isnot0 = λ x → not (is0 x)

-- szorzat tipusok
--\x ≡ ×
--proj\_1 ≡ proj₁ 

flip : ℕ × Bool → Bool × ℕ
flip = λ p → proj₂ p , proj₁ p

curry : (ℕ × Bool → ℕ) → (ℕ → Bool → ℕ)
curry = {!!}

uncurry : (ℕ → Bool → ℕ) → (ℕ × Bool → ℕ)
uncurry = {!!}

-- ehhez nem tudjuk a fenti uncurry-t hasznalni:
plus : ℕ × ℕ → ℕ
plus = {!!}

fac : ℕ → ℕ
fac = λ n → proj₂ (rec {A = ℕ × ℕ} (0 , 1) (λ p →  suc (proj₁ p) , (proj₂ p * (suc (proj₁ p)))) n)

-- ha x = 0,     akkor                fac 0       = 1
-- ha x = suc n, akkor tfh y = fac n, fac (suc n) = fac n * suc n = y * suc n
-- Nálunk:
--                         y = proj₂ p
--                         n = proj₁ p

fib : ℕ → ℕ
fib = λ n → proj₁ (rec {A = ℕ × ℕ} (1 , 1) (λ w → (proj₂ w , proj₁ w + proj₂ w)) n)

-- sum n = szamok osszege 0-tol (n-1)-ig
sum : ℕ → ℕ
sum = {!!}

pred : ℕ → ℕ
pred = λ n → proj₂ (rec {A = ℕ × ℕ} ( 0 , 0) (λ p → suc (proj₁ p) , proj₁ p) n)

-- 0: 0 , 0
-- 1: 0 , 0 → 1 , 0
-- 2: 1 , 0 → 2 , 1

and : Bool → Bool → Bool
and = λ b c → if b then c else false

is1 : ℕ → Bool
is1 = λ x → and (is0 (pred x)) (isnot0 x)

is2 : ℕ → Bool
is2 = λ x → is1 (pred x)

step : (ℕ → Bool) → (ℕ → Bool)
step = λ f n → if is0 n then false else f (pred n)

is3 = step is2

eq : ℕ → ℕ → Bool
eq = rec is0 step

-- tests

test0 : Eq ℕ (plus3 4) 7
test0 = refl

test1 : Eq ℕ (plus3 10) 13
test1 = refl

test0' : Eq ℕ (plus3' 4) 7
test0' = refl

test1' : Eq ℕ (plus3' 10) 13
test1' = refl

test2 : Eq ℕ (times2 3) 6
test2 = refl

test3 : Eq ℕ (times2 5) 10
test3 = refl

test4 : Eq ℕ (4 *3+2) 14
test4 = refl

test5 : Eq ℕ (1 *3+2) 5
test5 = refl

test6 : Eq ℕ (3 + 5) 8
test6 = refl

test7 : Eq ℕ (2 + 9) (5 + 6)
test7 = refl

test8 : Eq ℕ (3 * 5) 15
test8 = refl

test9 : Eq ℕ (5 * 8) 40
test9 = refl

test10 : Eq ℕ (3 ^ 3) 27
test10 = refl

test11 : Eq ℕ (2 ^ 10) 1024
test11 = refl

test12 : Eq ℕ (2 ^ 0) 1
test12 = refl

testpred1 : Eq ℕ (pred 0) 0
testpred1 = refl

testpred2 : Eq ℕ (pred 1000) 999
testpred2 = refl

testfac1 : Eq ℕ (fac 0) 1
testfac1 = refl

testfac2 : Eq ℕ (fac 3) 6
testfac2 = refl

testfac3 : Eq ℕ (fac 9) 362880
testfac3 = refl

testfib1 : Eq ℕ (fib 0) 1
testfib1 = refl

testfib2 : Eq ℕ (fib 5) 8
testfib2 = refl

testfib3 : Eq ℕ (fib 9) 55
testfib3 = refl

testsum1 : Eq ℕ (sum 0) 0
testsum1 = {!!}

testsum2 : Eq ℕ (sum 5) 10
testsum2 = {!!}

testsum3 : Eq ℕ (sum 11) 55
testsum3 = {!!}

testis1a : Eq Bool (is1 1) true
testis1a = refl

testis1b : Eq Bool (is1 10) false
testis1b = refl

testis1c : Eq Bool (is1 0) false
testis1c = refl

testis2a : Eq Bool (is2 2) true
testis2a = refl

testis2b : Eq Bool (is2 10) false
testis2b = refl

testis2c : Eq Bool (is2 1) false
testis2c = refl

testis2d : Eq Bool (is2 0) false
testis2d = refl

testis3a : Eq Bool (is3 3) true
testis3a = refl

testis3a' : Eq Bool (is3 4) false
testis3a' = refl

testis3b : Eq Bool (is3 10) false
testis3b = refl

testis3c : Eq Bool (is3 2) false
testis3c = refl

testis3d : Eq Bool (is3 1) false
testis3d = refl

testeq1 : Eq Bool (eq 7 8) false
testeq1 = refl

testeq2 : Eq Bool (eq 8 8) true
testeq2 = refl

testeq3 : Eq Bool (eq 1 80) false
testeq3 = refl

testeq4 : Eq Bool (eq 80 1) false
testeq4 = refl
