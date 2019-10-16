
open import lib

-- Set, függő függvények, ℕ-indukció
------------------------------------------------------------

-- std lib kiegészítés
infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
_+_ = λ n m → primrec n (λ _ n+m → suc n+m) m

BoolInd : (P : Bool → Set) → P true → P false → (b : Bool) → P b
BoolInd P pt pf true  = pt
BoolInd P pt pf false = pf

ℕInd : ∀{i}(P : ℕ → Set i) → P zero → ((n : ℕ) → P n → P (suc n))
       → (n : ℕ) → P n
ℕInd P pz ps zero    = pz
ℕInd P pz ps (suc n) = ps n (ℕInd P pz ps n)

-- Ismétlés:
-- definiáld a függvényt, ami egy ℕ-ból "inj₁ tt"-t ad, ha a szám 0,
-- ha a szám "suc n", akkor pedig "inj₂ n"-et ad.
isZero : ℕ → ⊤ ⊎ ℕ
isZero = {!!}

-- definiáld az if_then_else_ függvényt újra a
-- BoolInd segítségével!
-- pl: ITE ℕ true 0 10 = 0
ITE : (A : Set) → Bool → A → A → A
ITE = {!!}

-- típusok n-szerese
infix 3 _^_
_^_ : Set → ℕ → Set
_^_ = λ A n → primrec ⊤ (λ _ A^n → A × A^n) n

-- példa:
b4 : Bool ^ 4    -- C-u-C-u-C-c-C-,
b4 = true , (false , (true , (false , tt)))

-- definiáld újra a primrec-et, ℕInd felhasználásával!
primrec' : (A : Set) → A → (ℕ → A → A) → ℕ → A
primrec' = {!!}

-- definiáld a következő függvényt ℕ-indukcióval!
replicate : (A : Set) → (n : ℕ) → A → A ^ n
replicate = {!!}

-- definiáljuk a természetes számok egyenlőségét típusként
-- "ℕEq n m"-nek pontosan akkor van eleme, ha n egyenlő m-el.
ℕEq : ℕ → ℕ → Set
ℕEq = primrec
        (primrec ⊤ λ _ _ → ⊥)
        (λ n ℕEqn → primrec ⊥ (λ m _ → ℕEqn m))


-- definiáld a következő függvényt ℕInd-el:
ℕEqRefl : (n : ℕ) → ℕEq n n
ℕEqRefl = {!!}

-- bónusz feladat: definiáld a következő függvényt ℕ-indukcióval!  legyen a
-- végeredmény a két bemenő vektor egymás után füzése!
append : (A : Set)(n m : ℕ) → A ^ n → A ^ m → A ^ (n + m)
append = {!!}
