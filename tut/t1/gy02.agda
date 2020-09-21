{-# OPTIONS --no-pattern-match #-}

module tut.t1.gy02 where

open import lib

-- termeszetes szamok

-- introduction
-- zero : ℕ ℕ = \bN
-- if t : ℕ then suc t : ℕ
-- elimination
-- if u : A, v : A → A, t : ℕ, rec u v t : A
-- computation
-- rec u v zero = u
-- rec u b (suc t) = v (rec u v t)
-- example: rec u v (suc (suc zero)) = v (rec u v (suc zero)) = v (v (rec u v zero)) = v (v u)

-- C-u, C-u, C-c, C-, : show goal and context, fully normalized
-- C-u, C-u, C-c, C-. : show goal, inferred type of given expression, and context, fully normalized

three = suc (suc (suc zero))

seventyseven : ℕ
seventyseven = 77

-- teszteld oket!

plus3 : ℕ → ℕ
plus3 = λ n → suc (suc (suc n))
  
times2 : ℕ → ℕ
times2 = rec zero λ n → suc (suc n)

times2' : ℕ → ℕ
times2' = λ n → rec n suc n

-- _ in a program name means, we can write the parameter there → mixfix notation
_*3+2 : ℕ → ℕ
_*3+2 = rec (suc (suc zero)) λ n → suc (suc (suc n))

-- 0 + 100000 and 100000 + 0 yield the same result
-- but one is slower than the other, we do recursion on the second parameter
_+_ : ℕ → (ℕ → ℕ)
_+_ = λ x → rec x suc

-- try to give an alternative defininition:

_+'_ : ℕ → ℕ → ℕ
_+'_ = rec {!!} {!!}

-- we can write sections
_*_ : ℕ → (ℕ → ℕ)
_*_ = λ x → rec zero (_+ x)

_^_ : ℕ → (ℕ → ℕ)
_^_ = λ x → rec (suc zero) (_* x)

-- mi a kulonbseg az alabbi ket fuggveny kozott?

idℕ : ℕ → ℕ
idℕ = λ x → x

idℕ' : ℕ → ℕ
idℕ' = λ x → rec zero suc x

-- sokkal lassabban typecheckel, ha idℕ helyett idℕ' van: (nem vicc)

testid : Eq ℕ (idℕ 10000000) 10000000
testid = refl

-- ez konnyu:

is0 : ℕ → Bool
is0 = rec true λ _ → false

not : Bool → Bool 
not = λ x → if x then false else true

isEven : ℕ → Bool
isEven = rec true not 

isnot0 : ℕ → Bool
isnot0 = λ n → not (is0 n)

-- szorzat tipusok
-- if A, B are types then so is A × B ----- × = \x
-- introduction
-- if u : A, v : B then u , b : A × B
-- elimination
-- if t : A × B then proj₁ t : A      ------ ₁ = \_1
-- if t : A × B then proj₂ t : B
-- computation
-- proj₁ (u , v) = u
-- proj₂ (u , v) = v
-- uniqueness
-- (proj₁ t , proj₂ t) = t

flip : ℕ × Bool → Bool × ℕ
flip = λ t → (proj₂ t) , (proj₁ t)

curry : (ℕ × Bool → ℕ) → (ℕ → (Bool → ℕ)) -- is the same as (ℕ × Bool → ℕ) → ℕ → Bool → ℕ
                                          -- → is right associative
curry = λ f n b → f (n , b)               -- λ f n b → t is the same as λ f → λ n → λ b → t

uncurry : (ℕ → Bool → ℕ) → (ℕ × Bool → ℕ)
uncurry = λ f t → f (proj₁ t) (proj₂ t)

-- ehhez nem tudjuk a fenti uncurry-t hasznalni:
plus : ℕ × ℕ → ℕ
plus = λ t → proj₁ t + proj₂ t

-- rec : A → (A → A) → ℕ → A
-- A can't be ℕ, we need extra information for each recursive call (like introducing a local variable in a loop)
-- A = ℕ × ℕ here
-- A is an implicit parameter, if Agda doesn't figure it out, we have to give it explicitly
fac : ℕ → ℕ
fac = λ n → proj₂ (rec {A = ℕ × ℕ} (zero , suc zero) (λ t → suc (proj₁ t) , (suc (proj₁ t) * proj₂ t)) n)

fib : ℕ → ℕ
fib = λ x → proj₂ (rec {A = ℕ × ℕ}( 0  , 1) ( λ y → ( proj₂ y , proj₁ y + proj₂ y  )) x )

-- sum n = szamok osszege 0-tol (n-1)-ig
sum : ℕ → ℕ
sum = λ n → proj₂ (rec {A = ℕ × ℕ} (zero , zero) (λ t → suc (proj₁ t) , (proj₁ t + proj₂ t)) n )

pred : ℕ → ℕ
pred = λ n → proj₂ (rec {A = Bool × ℕ} (true , zero) (λ t → false , if proj₁ t then zero else suc (proj₂ t)) n)

and : Bool → Bool → Bool
and = λ b c → if b then c else false

is1 : ℕ → Bool
is1 = λ n → and (is0 (pred n)) (not (is0 n))

is2 : ℕ → Bool
is2 = λ n → is1 (pred n)

-- computes is(n+1) from isn
step : (ℕ → Bool) → (ℕ → Bool)
step = λ isn n → and (isn (pred n)) (not (isn n))

is3 = step is2

eq : ℕ → ℕ → Bool
eq = rec is0 step

-- tests

test0 : Eq ℕ (plus3 4) 7
test0 = refl

test1 : Eq ℕ (plus3 10) 13
test1 = refl

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
testsum1 = refl

testsum2 : Eq ℕ (sum 5) 10
testsum2 = refl

testsum3 : Eq ℕ (sum 11) 55
testsum3 = refl

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
