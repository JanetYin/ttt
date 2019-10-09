
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

-- egyenlőségvizsgálat Bool-al
eq : ℕ → ℕ → Bool
eq = {!primrec!}

lessThan : ℕ → ℕ → Bool
lessThan = {!!}


-- Set, függő függvények, ℕ-indukció
------------------------------------------------------------

-- definiáld az if_then_else_ függvény újra a következő típussal:
-- pl: ITE ℕ true 0 10 = 0

ITE : (A : Set) → Bool → A → A → A
ITE = {!!}

-- ezzel ne fogalkozz, csak megadjuk a ℕ-indukciót későbbi használatra
ℕInd : ∀{i}(P : ℕ → Set i) → P zero → ((n : ℕ) → P n → P (suc n))
       → (n : ℕ) → P n
ℕInd P pz ps zero    = pz
ℕInd P pz ps (suc n) = ps n (ℕInd P pz ps n)


-- definiáld (lásd: előadás) a következő függvényt:
-- legyen A ^ n = A × A × ... × A × ⊤   (n-darab A-ból álló szorzat)
infix 3 _^_
_^_ : Set → ℕ → Set
_^_ = {!!}

-- definiáld újra a primrec-et, ℕInd felhasználásával!
primrec' : (A : Set) → A → (ℕ → A → A) → ℕ → A
primrec' = {!!}

-- definiáld a következő függvényt ℕ-indukcióval!
replicate : (A : Set) → (n : ℕ) → A → A ^ n
replicate = {!!}

-- definiáld a következő függvényt ℕ-indukcióval!
-- legyen a végeredmény a két bemenő vektor összefüzése!
append : (A : Set)(n m : ℕ) → A ^ n → A ^ m → A ^ (n + m)
append = {!!}
