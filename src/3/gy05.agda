module gy05 where

open import Lib hiding (fromℕ)
open import Lib.Containers.Vector hiding (head; tail; map; length; _++_)
open import Lib.Containers.List hiding (head; tail; map; _++_; filter)

-- Vec and Fin
{-
infixr 5 _∷_
data Vec (A : Set) : ℕ → Set where
  []  : Vec' A 0
  _∷_ : {k : ℕ} → A → Vec A k → Vec A (suc k)
-}

head : {A : Set}{n : ℕ} → Vec A (suc n) → A
head (x ∷ xs) = x

tail : {A : Set}{n : ℕ} → Vec A (suc n) → Vec A n
tail (x ∷ xs) = xs

countDownFrom : (n : ℕ) → Vec ℕ n
countDownFrom zero = []
countDownFrom x@(suc n) = x ∷ countDownFrom n

test-countDownFrom : countDownFrom 3 ≡ 3 ∷ 2 ∷ 1 ∷ []
test-countDownFrom = refl

fromList : {A : Set}(xs : List A) → Vec A (length xs)
fromList [] = []
fromList (x ∷ xs) = x ∷ fromList xs

_++_ : {A : Set}{m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : {A B : Set}{n : ℕ} → (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

{-
data Fin : ℕ → Set where  -- Fin n = n-elemu halmaz
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)
-}

f0 : Fin 0 → ⊥
f0 ()

f1-0 : Fin 1
f1-0 = zero {0}

f2-0 f2-1 : Fin 2
f2-0 = zero {1}
f2-1 = suc {1} (zero {0})

f3-0 f3-1 f3-2 : Fin 3
f3-0 = zero {2}
f3-1 = suc {2} (zero {1})
f3-2 = suc {2} (suc {1} (zero {0}))

f4-0 f4-1 f4-2 f4-3 : Fin 4
f4-0 = zero {3}
f4-1 = suc {3} (zero {2})
f4-2 = suc {3} (suc {2} (zero {1}))
f4-3 = suc {3} (suc {2} (suc {1} (zero {0})))

-- Lib-ben a unicode ‼ az indexelés. \!! = ‼
infixl 10 _!!_
_!!_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A
[] !! ()
(x ∷ xs) !! zero = x
(x ∷ xs) !! suc n = xs !! n

test-!! : (the ℕ 3 ∷ 4 ∷ 1 ∷ []) !! (suc (suc zero)) ≡ 1
test-!! = refl

test2-!! : (the ℕ 3 ∷ 4 ∷ 1 ∷ 0 ∷ 10 ∷ []) !! 3 ≡ 0 -- 3-as literál a !! után valójában Fin 5 típusú.
test2-!! = refl

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero = 0
fromℕ (suc n) = suc (fromℕ n)

test-fromℕ : fromℕ 3 ≡ suc (suc (suc zero))
test-fromℕ = refl

-- Ez egy jó házi feladat, nem egyszerű!
tabulate : {n : ℕ}{A : Set} → (Fin n → A) → Vec A n
tabulate = {!!}

-- Sigma types

filter : {A : Set}{n : ℕ}(f : A → Bool) → Vec A n → Σ ℕ (λ k → Vec A k)
filter p [] = 0 , []
filter p (x ∷ xs) with p x
... | true  = let (k , ys) = filter p xs in suc k , x ∷ ys
... | false = filter p xs

-- Σ A (λ _ → B) ≡ A × B

test-filter : filter {ℕ} (3 <ᵇ_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ (2 , 4 ∷ 5 ∷ [])
test-filter = refl

-- A sima length kevés, abban csúnya dolgokat leírhatok, pl:
{-
length' : ∀{i}{A : Set i}{n : ℕ} → Vec A n → ℕ
length' xs = 0
-}
-- és akkor nagyon nem a vektor hosszát adja vissza.

smarterLength : ∀{i}{A : Set i}{n : ℕ} → Vec A n → Σ ℕ (λ k → n ≡ k)
smarterLength {n = k} xs = k , refl

minMax' : ℕ → ℕ → ℕ × ℕ
minMax' n m = {!   !}

-- Ugyanez sokkal jobban, de leginkább pontosabban.
-- Az előző változatban vissza tudok adni csúnya dolgokat is.
-- Pl. konstans (0 , 0)-t.
minMax : (n m : ℕ) → {!   !}
minMax n m = {!   !}