module zh04' where
open import lib

_+_ : ℕ → ℕ → ℕ
_+_ = λ x y → rec x suc y

_*_ : ℕ → ℕ → ℕ
_*_ = λ x y → rec 0 (_+_ x) y

-- Task1: Definiáld a hatványozást
_^_ : ℕ → ℕ → ℕ
x ^ y = rec 1 (λ a → a * x) y

test10 : Eq ℕ (3 ^ 3) 27
test10 = refl
test11 : Eq ℕ (2 ^ 10) 1024
test11 = refl
test12 : Eq ℕ (2 ^ 0) 1
test12 = refl

task1 = _^_


-- Task2: Definiáld azt a függvényt, ami tt-t ad vissza ha egy szám 0, és ff-et ha a szám >0

_=0 : ℕ → 𝟚
-- x =0 = rec tt (λ k → ff) x
zero    =0 = tt
(suc _) =0 = ff

test⠀=0⠀1 : Eq 𝟚 (0 =0) tt
test⠀=0⠀1 = refl
test⠀=0⠀2 : Eq 𝟚 (1 =0) ff
test⠀=0⠀2 = refl
test⠀=0⠀3 : Eq 𝟚 (2 =0) ff
test⠀=0⠀3 = refl

task2 = _=0
