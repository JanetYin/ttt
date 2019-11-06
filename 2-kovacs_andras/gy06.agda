
open import lib

-- Ismétlés:
-- definiáld a függvényt, ami egy ℕ-ból "inj₁ tt"-t ad, ha a szám 0,
-- ha a szám "suc n", akkor pedig "inj₂ n"-et ad.
isZero : ℕ → ⊤ ⊎ ℕ
isZero = λ n → primrec (inj₁ tt) (λ n _ → inj₂ n) n

-- órai feladat megoldás
-- _-_ korábbi definíció: primrec m-en
--     iteráljuk pred függvényt n-en.
infixl 6 _-_
_-_ : ℕ → ℕ → ⊤ ⊎ ℕ
_-_ = λ n m →
  primrec
    -- ha m = 0, akkor nincs underflow
    (inj₂ n)
    -- ha m = suc m
    -- tudjuk n-m-et, szeretnénk megadni
    --  n-(suc m) -et.
    (λ m n-m → case n-m
      (λ _   → inj₁ tt)
      (λ n-m → case (isZero n-m)
        (λ _ → inj₁ tt)
        (λ x → inj₂ x)))
    m

_-'_ : ℕ → ℕ → ⊤ ⊎ ℕ
_-'_ = λ n m →
  primrec
    -- ha m = 0, akkor eredmény inj₂ n
    (λ n → inj₂ n)
    -- ha m = suc m, akkor kapunk egy
    -- subm függvény, ami kivon m-et egy számból
    (λ m subm n →
      case (isZero n)
        (λ _ → inj₁ tt)
        (λ n → subm n))
    m n

-- tesztek működnek
-- infixl 3 _≡_
-- data _≡_ {A : Set}(a : A) : A → Set where
--   refl : a ≡ a

-- test1 : 0 - 0 ≡ inj₂ 0
-- test1 = refl
-- test2 : 0 - 1 ≡ inj₁ tt
-- test2 = refl
-- test3 : 3 - 4 ≡ inj₁ tt
-- test3 = refl
-- test4 : 5 - 4 ≡ inj₂ 1
-- test4 = refl




-- Set, függő függvények, ℕ-indukció
------------------------------------------------------------

-- std lib kiegészítés
infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
_+_ = λ n m → primrec n (λ _ n+m → suc n+m) m

BoolInd :
 (P : Bool → Set)
 → P true → P false
 → (b : Bool) → P b
BoolInd P pt pf true  = pt
BoolInd P pt pf false = pf

ℕInd : (P : ℕ → Set) → P zero → ((n : ℕ) → P n → P (suc n))
       → (n : ℕ) → P n
ℕInd P pz ps zero    = pz
ℕInd P pz ps (suc n) = ps n (ℕInd P pz ps n)

-- definiáld az if_then_else_ függvényt újra a
-- BoolInd segítségével!
-- pl: ITE ℕ true 0 10 = 0
ITE : (A : Set) → Bool → A → A → A
ITE = λ A b t f → BoolInd (λ _ → A) t f b

-- típusok n-szerese
infix 3 _^_
_^_ : Set → ℕ → Set
_^_ = λ A n → primrec
  ⊤                   -- A^0 = ⊤
  (λ _ A^n → A × A^n) -- A^suc n = A × A^n
  n

-- példa: ℕ ^ 4 = ℕ × ℕ × ℕ × ℕ × ⊤
n4 : ℕ ^ 4
n4 = 0 , (3 , (2 , (3 , tt)))

-- példa:
b4 : Bool ^ 4    -- C-u-C-u-C-c-C-,
b4 = true , (false , (true , (false , tt)))

-- definiáld újra a primrec-et, ℕInd felhasználásával!
primrec' : (A : Set) → A → (ℕ → A → A) → ℕ → A
primrec' = λ A z s n → ℕInd (λ _ → A) z s n

-- ha olyat látunk: λ x → f x ahol (x ∉ f)
--   egyenlő azzal: f

-- egyediségi szabály alapján:
-- primrec' = λ A → ℕInd (λ _ → A)

-- definiáld a következő függvényt ℕ-indukcióval!
replicate : (A : Set) → (n : ℕ) → A → A ^ n
replicate = λ A n a →
  ℕInd (λ n → A ^ n) -- szeretnénk minden n-re A^n
                     -- típusú eredmnyt kapni
       tt    -- cél: A^0
             -- viszont A^0 = ⊤ (_^_ definíció szerint)

       -- van egy A ^ n típusú értékünk, szeretnénk
       -- A ^ suc n típusú értéket.
       (λ n A^n → a , A^n)
       n
-- tehát: replicate A n a eléfűzi n-szer tt-nek
--        a-t.

-- Haskell-ben:
-- replicate :: Int -> a -> [a]
-- replicate 3 True = [True, True, True]

-- definiáljuk a természetes számok egyenlőségét típusként
-- "ℕEq n m"-nek pontosan akkor van eleme, ha n egyenlő m-el.

ℕEq : ℕ → ℕ → Set
ℕEq = λ n → primrec
  -- ha n = 0
  (λ m → case (isZero m) (λ _ → ⊤) (λ _ → ⊥))
  -- ha m = suc m
  (λ m ℕEqm n → case (isZero n)
    (λ _ → ⊥)
    (λ n → ℕEqm n))
  n

-- primrec
--         (primrec ⊤ λ _ _ → ⊥)
--         (λ n ℕEqn → primrec ⊥ (λ m _ → ℕEqn m))

-- (ℕEq n m)-nek pontosan akkor van értéke,
-- ha n és m azonos

-- példa:

p1 : ℕEq 10 10
p1 = tt

p2 : ℕEq 100 100
p2 = tt

p3 : ¬ ℕEq 0 1
p3 = λ p → p


-- definiáld a következő függvényt ℕInd-el:
ℕEqRefl : (n : ℕ) → ℕEq n n
ℕEqRefl = {!!}

-- + szimmetrikus, tranzitív

-- bónusz feladat: definiáld a következő függvényt ℕ-indukcióval!  legyen a
-- végeredmény a két bemenő vektor egymás után füzése!
append : (A : Set)(n m : ℕ) → A ^ n → A ^ m → A ^ (n + m)
append = {!!}
