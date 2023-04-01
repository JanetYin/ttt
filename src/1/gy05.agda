module gy05 where

open import lib

-- Vec and Fin
infixr 5 _∷_
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

single : Vec Bool 1
single = true ∷ []

head : {A : Set}{n : ℕ} → Vec A (suc n) → A
head (x ∷ xs) = x

tail : {A : Set}{n : ℕ} → Vec A (suc n) → Vec A n
tail (x ∷ xs) = xs

countDownFrom : (n : ℕ) → Vec ℕ n
countDownFrom zero    = []
countDownFrom (suc n) = suc n ∷ countDownFrom n

test-countDownFrom : countDownFrom 3 ≡ 3 ∷ 2 ∷ 1 ∷ []
test-countDownFrom = refl

take : {A : Set}{n : ℕ} → (m : ℕ) → Vec A (m + n) → Vec A m
take zero xs = []
take (suc m) (x ∷ xs) = x ∷ take m xs

data Fin : ℕ → Set where  -- Fin n = n-elemu halmaz
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

f0 : Fin 0 → ⊥
f0 ()

f1-0 : Fin 1
f1-0 = zero

f2-0 f2-1 : Fin 2
f2-0 = zero {1}
f2-1 = suc {1} (zero {0})

f3-0 f3-1 f3-2 : Fin 3
f3-0 = {!!}
f3-1 = {!!}
f3-2 = {!!}

f4-0 f4-1 f4-2 f4-3 : Fin 4
f4-0 = {!!}
f4-1 = {!!}
f4-2 = {!!}
f4-3 = {!!}

infixl 9 _!!_
_!!_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A
[] !! i = exfalso (f0 i)
(x ∷ xs) !! zero = x
(x ∷ xs) !! suc i = xs !! i

test-!! : (zero ∷ 4 ∷ 1 ∷ []) !! (suc (suc zero)) ≡ 1
test-!! = refl

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ = {!!}

test-fromℕ : fromℕ 3 ≡ suc (suc (suc zero))
test-fromℕ = refl

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

map : {A B : Set}{n : ℕ} → (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

length : {A : Set} → List A → ℕ
length [] = 0
length (_ ∷ xs) = suc (length xs)

fromList : {A : Set}(xs : List A) → Vec A (length xs)
fromList [] = []
fromList (x ∷ xs) = x ∷ fromList xs

_++_ : {A : Set}{m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- Nem egyszerű, probléma lesz, új ötlet kell.
-- reverse

{-
A naív definíció nem működik.

reverse : {A : Set}{n : ℕ} → Vec A n → Vec A n
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ [])
-}

-- NEHÉZ FELADAT
tabulate : {n : ℕ}{A : Set} → (Fin n → A) → Vec A n
tabulate = {!!}

-- Sigma types

filter : {A : Set}{n : ℕ}(f : A → Bool) → Vec A n → Σ ℕ (Vec A)
filter = {!!}

test-filter : filter (3 <_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ (2 , 4 ∷ 5 ∷ [])
test-filter = refl
