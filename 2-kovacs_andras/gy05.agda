
open import lib

-- Természetes számok
------------------------------------------------------------

-- ℕ  \bN
isZero : ℕ → Bool
isZero = λ n → primrec
  -- mit adjunk vissza 0 esetén
  true
  -- mit adjunk vissza (suc n) esetén
  (λ _ _ → false)  -- NINCS szükség rekurzív hívásra
  n

-- A pred ("predecessor") függvény 1-et kivon egy számból, 0-ra 0-t ad.
pred : ℕ → ℕ
pred = λ n → primrec
  zero
  (λ n _ → n) -- itt sem használjuk a rekurzív hívást
              -- mivel n éppen a megelőző ℕ
  n

-- bónusz házi: pred, viszont nem használhatjuk
-- a suc eset első paraméterét!
pred' : ℕ → ℕ
pred' = {!!}


-- A kivonás 0-t ad vissza, ha egész számokon negatív lenne az eredmény.

-- Iterált pred alkalmazás
infixl 6 _-_
_-_ : ℕ → ℕ → ℕ
_-_ = λ n m → primrec
  n                     -- n - 0 = n
  (λ m n-m → pred n-m)  -- n - suc m = pred (n - m)
  m

-- suc-ot kell iterálni!
infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
_+_ = λ n m → primrec n (λ _ n+m → suc n+m) m

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
_*_ = λ n m → primrec 0 (λ _ n*m → n + n*m) m

factorial : ℕ → ℕ
factorial = λ n → primrec 1 (λ n factn → suc n * factn) n

-- fact 0       = 1
-- fact (suc n) = suc n * fact n

-- egyenlőségvizsgálat Bool-al
-- alapötlet: min 4 eset vizsgálat
eq : ℕ → ℕ → Bool
eq =
  -- cél: ℕ → Bool függvény megadása, mindkét esetben
  λ n → primrec
   -- n = 0 : vizsgáljuk, hogy m = 0
   (λ m → isZero m)

   -- n = suc n : vizsgáljuk m-et
   (λ n eqn m →
      primrec
        -- m = 0
        false
        -- m = suc m : eredmény (eqn m)
        (λ m _ → eqn m)
        m)
   n

-- házi feladat (hasonló eq-hez)
lessThan : ℕ → ℕ → Bool
lessThan = {!!}
