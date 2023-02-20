
open import lib

-- Természetes számok
------------------------------------------------------------

isZero : ℕ → Bool
isZero = {!!}

-- A pred ("predecessor") függvény 1-et kivon egy számból, 0-ra 0-t ad.
pred : ℕ → ℕ
pred = {!!}

-- A kivonás 0-t ad vissza, ha egész számokon negatív lenne az eredmény.
infixl 6 _-_
_-_ : ℕ → ℕ → ℕ
_-_ = {!!}

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
_+_ = {!!}

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
_*_ = {!!}

factorial : ℕ → ℕ
factorial = {!!}

lessThan : ℕ → ℕ → Bool
lessThan = {!!}

-- bónusz feladat: Fibonacci függvény
fibonacci : ℕ → ℕ
fibonacci = {!!}

-- bónusz feladat: Ackermann függvény.
-- lásd: https://en.wikipedia.org/wiki/Ackermann_function
ack : ℕ → ℕ → ℕ
ack = {!!}


-- Logika
------------------------------------------------------------


-- bónusz feladat: a klasszikus logikai axiómák logikai ekvivalenciája.
-- Három megfogalmazás:

-- 1. kettős negáció elimináció
DNegElim = (A : Set) → ¬ ¬ A → ¬ A

-- 2. kizárt harmadik elve (law of excluded middle)
LEM = (A : Set) → A ⊎ ¬ A

-- 3. Peirce törvény
Peirce = (A B : Set) → ((A → B) → A) → A

-- tipp 1: elég csak az egyik irányt belátni mindenhol, mivel
-- akkor a másik irány megadtható úgy, hogy teszünk egy kört
-- a függvények komponálásával.
-- tipp 2: használjuk C-u-C-u-C-c-C-, parancsot a
-- kibontott típusok megjelenítésére.
DNegElim↔LEM : DNegElim ↔ LEM
DNegElim↔LEM = {!!}

LEM↔Peirce : LEM ↔ Peirce
LEM↔Peirce = {!!}

Peirce↔DNegElim : Peirce ↔ DNegElim
Peirce↔DNegElim = {!!}
