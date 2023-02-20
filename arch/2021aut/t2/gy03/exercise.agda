module 2021aut.t2.gy03.exercise where

open import lib

---------------------------------------------------------
-- Natural numbers
---------------------------------------------------------

three : ℕ
three = {!!}

seventyseven : ℕ
seventyseven = {!!}

-- teszteld oket!

plus3 : ℕ → ℕ
plus3 = λ x → suc (suc (suc x))

-- tesztek
test0 : Eq ℕ (plus3 4) 7
test0 = refl
test1 : Eq ℕ (plus3 10) 13
test1 = {!!}

times2 : ℕ → ℕ
times2 = {!!}

-- tesztek
test2 : Eq ℕ (times2 3) 6
test2 = {!!}
test3 : Eq ℕ (times2 5) 10
test3 = {!!}

-- x |-> x*3+2 fuggveny
_*3+2 : ℕ → ℕ
_*3+2 = {!!}

-- tesztek
test4 : Eq ℕ (4 *3+2) 14
test4 = {!!}
test5 : Eq ℕ (1 *3+2) 5
test5 = {!!}

-- osszeadas
_+_ : ℕ → (ℕ → ℕ)
_+_ = {!!}

test6 : Eq ℕ (3 + 5) 8
test6 = {!!}
test7 : Eq ℕ (2 + 9) (5 + 6)
test7 = {!!}

-- szorzas
_*_ : ℕ → (ℕ → ℕ)
_*_ = {!!}

test8 : Eq ℕ (3 * 5) 15
test8 = {!!}
test9 : Eq ℕ (5 * 8) 40
test9 = {!!}

-- hatvanyozas
_^_ : ℕ → (ℕ → ℕ)
_^_ = {!!}

test10 : Eq ℕ (3 ^ 3) 27
test10 = {!!}
test11 : Eq ℕ (2 ^ 10) 1024
test11 = {!!}
test12 : Eq ℕ (2 ^ 0) 1
test12 = {!!}

-- mi a kulonbseg az alabbi ket fuggveny kozott?

idℕ : ℕ → ℕ
idℕ = λ x → x

idℕ' : ℕ → ℕ
idℕ' = λ x → rec zero suc x

-- sokkal lassabban typecheckel, ha idℕ helyett idℕ' van:
testid : Eq ℕ (idℕ 10000000) 10000000
testid = refl

-- Ez csak nagyon-szorgalmi

is0 : ℕ → 𝟚
is0 = {!!}

not0 : ℕ → 𝟚
not0 = {!!}

isEven : ℕ → 𝟚
isEven = {!!}

isnot0 : ℕ → 𝟚
isnot0 = {!!}

---------------------------------------------------------
-- szorzat tipusok
---------------------------------------------------------

flip : ℕ × 𝟚 → 𝟚 × ℕ
--   (ℕ × 𝟚) → (𝟚 × ℕ)
flip = λ t → π₂ t , π₁ t

curry : {A B C : Set} → (A × B → C) → (A → B → C)
--curry = λ t g e → g
--curry = λ f → λ n b → f (n , b)
curry = λ t → λ g → λ e → t (g , e)

uncurry : (ℕ → 𝟚 → ℕ) → (ℕ × 𝟚 → ℕ)
uncurry = {!!}

-- ehhez nem tudjuk a fenti uncurry-t hasznalni:
plus : ℕ × ℕ → ℕ
plus = {!!}

fac : ℕ → ℕ
fac = {!!}

fac'' : ℕ → ℕ
fac'' n = π₁ (rec {Agda.Primitive.lzero} {ℕ × ℕ} (1 , 1) (λ p → ((π₁ p) * (π₂ p) , suc (π₂ p)) ) n)

testfac1 : Eq ℕ (fac 0) 1
testfac1 = refl
testfac2 : Eq ℕ (fac 3) 6
testfac2 = refl
testfac3 : Eq ℕ (fac 9) 362880
testfac3 = refl

fib : ℕ → ℕ
fib = {!!}

testfib1 : Eq ℕ (fib 0) 1
testfib1 = {!!}
testfib2 : Eq ℕ (fib 5) 8
testfib2 = {!!}
testfib3 : Eq ℕ (fib 9) 55
testfib3 = {!!}

-- sum n = szamok osszege 0-tol (n-1)-ig
sum : ℕ → ℕ
sum = {!!}

testsum1 : Eq ℕ (sum 0) 0
testsum1 = {!!}
testsum2 : Eq ℕ (sum 5) 10
testsum2 = {!!}
testsum3 : Eq ℕ (sum 11) 55
testsum3 = {!!}
