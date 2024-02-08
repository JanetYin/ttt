open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_+_; _*_; _-_; _<_)
open import Lib.Equality
open import Lib.Bool

-- Számold ki, hogy a paraméterek összege egyenlő-e 0-val.
-- Csak mintaillesztést használj.
sumIsZero : ℕ -> ℕ -> Bool
sumIsZero = {!!}
sumIsZeroTest1 : sumIsZero 0 0 ≡ true
sumIsZeroTest1 = refl
sumIsZeroTest2 : sumIsZero 0 11 ≡ false
sumIsZeroTest2 = refl

-- Számold ki, hogy a paraméter kisebb-e, mint 3.
-- A _<_ operátort ne használd itt.
isSmallerThan3 : ℕ -> Bool
isSmallerThan3 = {!!}
iST3test1 : isSmallerThan3 2 ≡ true
iST3test1 = refl
iST3test2 : isSmallerThan3 3 ≡ false
iST3test2 = refl
iST3test3 : isSmallerThan3 4 ≡ false
iST3test3 = refl

-- Számold ki a paraméter háromszorosát.
-- A szorzást ne használd itt.
triple : ℕ -> ℕ
triple = {!!}
tripleTest1 : triple 0 ≡ 0
tripleTest1 = refl
tripleTest2 : triple 1 ≡ 3
tripleTest2 = refl
tripleTest3 : triple 20 ≡ 60
tripleTest3 = refl

-- Számold ki a paraméter 3-as maradékát.
mod3 : ℕ -> ℕ
mod3 = {!!}
mod3Test1 : mod3 0 ≡ 0
mod3Test1 = refl
mod3Test2 : mod3 3 ≡ 0
mod3Test2 = refl
mod3Test3 : mod3 13 ≡ 1
mod3Test3 = refl
mod3Test4 : mod3 20 ≡ 2
mod3Test4 = refl

-- Írj egy függvényt, ami két ℕ-ot (n és m) vár, és a következőképp működik:
-- - ha n 4-es maradéka 1, adjon vissza m - 1-et, ha m nem 0 (ha 0, adjon vissza 0-t);
-- - ha n 4-es maradéka 3, adjon vissza m + 1-et;
-- - egyébként adja vissza m-et.
-- Csak mintaillesztést használj.
f : ℕ -> ℕ -> ℕ
f = {!!}
testf1 : ∀ (m : ℕ) -> f 8 m ≡ m
testf1 m = refl
testf2 : f 5 0 ≡ 0
testf2 = refl
testf25 : f 5 19 ≡ 18
testf25 = refl
testf3 : ∀ (m : ℕ) -> f 15 m ≡ suc m
testf3 m = refl
testf4 : ∀ (m : ℕ) -> f 10 m ≡ m
testf4 m = refl

-- **Nézd meg a gyakfájlból az even?-t, fibet, eq?-t.**
