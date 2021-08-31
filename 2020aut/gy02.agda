{-# OPTIONS --no-pattern-match #-}

module tut.gy02 where

open import lib

-- termeszetes szamok

three = {!!}

seventyseven : ℕ
seventyseven = {!!}

-- teszteld oket!

plus3 : ℕ → ℕ
plus3 = {!!}

times2 : ℕ → ℕ
times2 = {!!}

_*3+2 : ℕ → ℕ
_*3+2 = {!!}

_+_ : ℕ → (ℕ → ℕ)
_+_ = {!!}

_*_ : ℕ → (ℕ → ℕ)
_*_ = {!!}

_^_ : ℕ → (ℕ → ℕ)
_^_ = {!!}

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
is0 = {!!}

not = {!!}

isEven : ℕ → Bool
isEven = {!!}

isnot0 : ℕ → Bool
isnot0 = {!!}

-- szorzat tipusok

flip : ℕ × Bool → Bool × ℕ
flip = {!!}

curry : (ℕ × Bool → ℕ) → (ℕ → Bool → ℕ)
curry = {!!}

uncurry : (ℕ → Bool → ℕ) → (ℕ × Bool → ℕ)
uncurry = {!!}

-- ehhez nem tudjuk a fenti uncurry-t hasznalni:
plus : ℕ × ℕ → ℕ
plus = {!!}

fac : ℕ → ℕ
fac = {!!}

fib : ℕ → ℕ
fib = {!!}

-- sum n = szamok osszege 0-tol (n-1)-ig
sum : ℕ → ℕ
sum = {!!}

pred : ℕ → ℕ
pred = {!!}

and : Bool → Bool → Bool
and = λ b c → if b then c else false

is1 : ℕ → Bool
is1 = {!!}

is2 : ℕ → Bool
is2 = {!!}

step : (ℕ → Bool) → (ℕ → Bool)
step = {!!}

is3 = step is2

eq : ℕ → ℕ → Bool
eq = {!!}

-- tests

test0 : Eq ℕ (plus3 4) 7
test0 = {!!}

test1 : Eq ℕ (plus3 10) 13
test1 = {!!}

test2 : Eq ℕ (times2 3) 6
test2 = {!!}

test3 : Eq ℕ (times2 5) 10
test3 = {!!}

test4 : Eq ℕ (4 *3+2) 14
test4 = {!!}

test5 : Eq ℕ (1 *3+2) 5
test5 = {!!}

test6 : Eq ℕ (3 + 5) 8
test6 = {!!}

test7 : Eq ℕ (2 + 9) (5 + 6)
test7 = {!!}

test8 : Eq ℕ (3 * 5) 15
test8 = {!!}

test9 : Eq ℕ (5 * 8) 40
test9 = {!!}

test10 : Eq ℕ (3 ^ 3) 27
test10 = {!!}

test11 : Eq ℕ (2 ^ 10) 1024
test11 = {!!}

test12 : Eq ℕ (2 ^ 0) 1
test12 = {!!}

testpred1 : Eq ℕ (pred 0) 0
testpred1 = {!!}

testpred2 : Eq ℕ (pred 1000) 999
testpred2 = {!!}

testfac1 : Eq ℕ (fac 0) 1
testfac1 = {!!}

testfac2 : Eq ℕ (fac 3) 6
testfac2 = {!!}

testfac3 : Eq ℕ (fac 9) 362880
testfac3 = {!!}

testfib1 : Eq ℕ (fib 0) 1
testfib1 = {!!}

testfib2 : Eq ℕ (fib 5) 8
testfib2 = {!!}

testfib3 : Eq ℕ (fib 9) 55
testfib3 = {!!}

testsum1 : Eq ℕ (sum 0) 0
testsum1 = {!!}

testsum2 : Eq ℕ (sum 5) 10
testsum2 = {!!}

testsum3 : Eq ℕ (sum 11) 55
testsum3 = {!!}

testis1a : Eq Bool (is1 1) true
testis1a = {!!}

testis1b : Eq Bool (is1 10) false
testis1b = {!!}

testis1c : Eq Bool (is1 0) false
testis1c = {!!}

testis2a : Eq Bool (is2 2) true
testis2a = {!!}

testis2b : Eq Bool (is2 10) false
testis2b = {!!}

testis2c : Eq Bool (is2 1) false
testis2c = {!!}

testis2d : Eq Bool (is2 0) false
testis2d = {!!}

testis3a : Eq Bool (is3 3) true
testis3a = {!!}

testis3a' : Eq Bool (is3 4) false
testis3a' = {!!}

testis3b : Eq Bool (is3 10) false
testis3b = {!!}

testis3c : Eq Bool (is3 2) false
testis3c = {!!}

testis3d : Eq Bool (is3 1) false
testis3d = {!!}

testeq1 : Eq Bool (eq 7 8) false
testeq1 = {!!}

testeq2 : Eq Bool (eq 8 8) true
testeq2 = {!!}

testeq3 : Eq Bool (eq 1 80) false
testeq3 = {!!}

testeq4 : Eq Bool (eq 80 1) false
testeq4 = {!!}
