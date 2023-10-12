module gy05 where

open import Lib hiding (fromℕ)
open import Lib.Containers.Vector hiding (head; tail; map; length; _++_)
open import Lib.Containers.List hiding (head; tail; map; _++_; filter)

-- Vec and Fin
{-
infixr 5 _∷_
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)
-}
head : {A : Set}{n : ℕ} → {!   !}
head = {!!}

tail : {A : Set}{n : ℕ} → {!   !}
tail = {!!}

countDownFrom : (n : ℕ) → Vec ℕ n
countDownFrom = {!!}

test-countDownFrom : countDownFrom 3 ≡ 3 ∷ 2 ∷ 1 ∷ []
test-countDownFrom = refl

fromList : {A : Set}(xs : List A) → Vec A (length xs)
fromList xs = {!!}

_++_ : {A : Set}{m n : ℕ} → {!   !} → {!   !} → {!   !}
xs ++ ys = {!!}

map : {!   !}
map f xs = {!!}

{-
data Fin : ℕ → Set where  -- Fin n = n-elemu halmaz
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)
-}
f0 : Fin 0 → ⊥
f0 x = {!!}

f1-0 : Fin 1
f1-0 = {!!}

f2-0 f2-1 : Fin 2
f2-0 = {!!}
f2-1 = {!!}

f3-0 f3-1 f3-2 : Fin 3
f3-0 = {!!}
f3-1 = {!!}
f3-2 = {!!}

f4-0 f4-1 f4-2 f4-3 : Fin 4
f4-0 = {!!}
f4-1 = {!!}
f4-2 = {!!}
f4-3 = {!!}

-- Lib-ben a unicode ‼ az indexelés. \!! = ‼
infixl 10 _!!_
_!!_ : {A : Set}{n : ℕ} → {!   !}
xs !! n = {!!}

test-!! : (the ℕ 3 ∷ 4 ∷ 1 ∷ []) !! (suc (suc zero)) ≡ 1
test-!! = refl

test2-!! : (the ℕ 3 ∷ 4 ∷ 1 ∷ 0 ∷ 10 ∷ []) !! 3 ≡ 0 -- 3-as literál a !! után valójában Fin 5 típusú.
test2-!! = refl

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ = {!!}

test-fromℕ : fromℕ 3 ≡ suc (suc (suc zero))
test-fromℕ = refl

-- Ez egy jó házi feladat, nem egyszerű!
tabulate : {n : ℕ}{A : Set} → (Fin n → A) → Vec A n
tabulate = {!!}

-- Sigma types

filter : {A : Set}{n : ℕ}(f : A → Bool) → Vec A n → Σ ℕ (Vec A)
filter = {!!}

test-filter : filter {ℕ} (3 <ᵇ_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ (2 , 4 ∷ 5 ∷ [])
test-filter = refl

smarterLength : ∀{i}{A : Set i}{n : ℕ} → Vec A n → ?
smarterLength = {!   !}

minMax' : ℕ → ℕ → ℕ × ℕ
minMax' n m = {!   !}

-- Ugyanez sokkal jobban, de leginkább pontosabban.
-- Az előző változatban vissza tudok adni csúnya dolgokat is.
-- Pl. konstans (0 , 0)-t.
minMax : (n m : ℕ) → ?
minMax n m = {!   !}