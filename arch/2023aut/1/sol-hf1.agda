module sol-hf1 where
open import Lib
open import Lib.Sigma.Type

--- 1. feladat
--- Írj egy függvényt, ami kettővel növeli az adott számot
--- CSAK A suc FÜGGVÉNYT HASZNÁLD

plus2 : ℕ → ℕ
plus2 x = suc (suc x)

--- 2. feladat
--- Írj egy függvényt, ami négyszeresére növeli a számot
--- CSAK A suc FÜGGVÉNYT HASZNÁLD

times4 : ℕ → ℕ
times4 zero = zero
times4 (suc x) = suc (suc (suc (suc (times4 x))))

--- 3. feladat
--- Írjad meg a `prede` függvényt. Ez a függvény visszadja a bemeneti paramétert megelőző (-1-es) számot. 0 esetén 0 adjon vissza!
--- A FELADATOT CSAK MINTAILESZTÉSSEL OLD MEG

prede : ℕ → ℕ
prede zero = zero
prede (suc x) = x

--- 4. feladat
--- Írd meg a Haskell-ből jól ismert $ függvényt!
_$_ : (ℕ → ℕ) → ℕ → ℕ
--vigyázz, csalok! ;)
_$_ f = f

--- TESZTEK
--- NE ÍRD ÁT

infixr 6 _$_

testp0 : 2 ≡ plus2 0
testp1 : 4 ≡ plus2 2
testp2 : 70 ≡ plus2 68
testp0 = refl
testp1 = refl
testp2 = refl

testt0 : 4 ≡ times4 1
testt1 : 44 ≡ times4 11
testt2 : 0 ≡ times4 0
testt0 = refl
testt1 = refl
testt2 = refl

applyTimes : (ℕ → ℕ) → ℕ → ℕ → ℕ
applyTimes _ zero x = x
applyTimes f (suc t) x = f (applyTimes f t x)

testpr0 : prede (prede (prede (prede 2))) ≡ 0
testpr1 : prede 100 ≡ 99
testpr2 : prede (prede 7) ≡ 5
testpr0 = refl
testpr1 = refl
testpr2 = refl

test$0 : (λ x → x) $ 10 ≡ 10
test$1 : (5 +_) $ 25 ≡ 30
test$2 : (_* 3) $ 7 ≡ 21
test$0 = refl
test$1 = refl
test$2 = refl

