open import Lib hiding (fromℕ)
open import Lib.Containers.Vector.Type
open import Lib.Containers.List.Type

-- Vec and Fin
{-
infixr 5 _∷_
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)
-}
head : {A : Set}{n : ℕ} → Vec A (suc n) → A
head (x ∷ xs) = x

tail : {A : Set}{n : ℕ} → Vec A (suc n) → Vec A n
tail (x ∷ xs)  = xs

countDownFrom : (n : ℕ) → Vec ℕ n
countDownFrom zero = []
countDownFrom (suc n) = suc n ∷ countDownFrom n

test-countDownFrom : countDownFrom 3 ≡ 3 ∷ 2 ∷ 1 ∷ []
test-countDownFrom = refl

{-
data Fin : ℕ → Set where  -- Fin n = n-elemu halmaz
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)
-}
f0 : Fin 0 → ⊥
f0 ()

f1-0 : Fin 1
f1-0 = zero

f2-0 f2-1 : Fin 2
f2-0 = zero
f2-1 = suc zero

f3-0 f3-1 f3-2 : Fin 3
f3-0 = {!!}
f3-1 = {!!}
f3-2 = {!!}

f4-0 f4-1 f4-2 f4-3 : Fin 4
f4-0 = {!!}
f4-1 = {!!}
f4-2 = {!!}
f4-3 = {!!}

-- Lib-ben a unicode ‼ az indexelés.
infixl 9 _!!_
_!!_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A
(x ∷ xs) !! zero = x
(x ∷ xs) !! suc n = xs !! n

test-!! : (the ℕ 3 ∷ 4 ∷ 1 ∷ []) !! (suc (suc zero)) ≡ 1
test-!! = refl

test2-!! : (the ℕ 3 ∷ 4 ∷ 1 ∷ 0 ∷ 10 ∷ []) !! 3 ≡ 0 -- 3-as literál a !! után valójában Fin 5 típusú.
test2-!! = refl

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero = zero
fromℕ (suc n) = suc (fromℕ n)

test-fromℕ : fromℕ 3 ≡ suc (suc (suc zero))
test-fromℕ = refl

map : {A B : Set}(f : A → B){n : ℕ} → Vec A n → Vec B n
map f [] = []
map f (x ∷ as) = f x ∷ map f as

{-
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A
-}

length : {A : Set} → List A → ℕ
length [] = 0
length (x ∷ xs) = suc (length xs)

fromList : {A : Set}(as : List A) → Vec A (length as)
fromList [] = []
fromList (x ∷ as) = x ∷ fromList as

_++_ : {A : Set}{m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
[] ++ xs = xs
(x ∷ ys) ++ xs = x ∷ (ys ++ xs)

tabulate : {n : ℕ}{A : Set} → (Fin n → A) → Vec A n
tabulate {zero} f = []
tabulate {suc n} f = f zero ∷ tabulate (λ x → f (suc x))

-- Sigma types

filter : {A : Set}{n : ℕ}(f : A → Bool) → Vec A n → Σ ℕ (Vec A)
filter f [] = zero , []
filter f (x ∷ xs) with f x
... | false = filter f xs
... | true with filter f xs
... | n , vs = suc n , (x ∷ vs)

test-filter : filter {ℕ} (3 <ᵇ_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ (2 , 4 ∷ 5 ∷ [])
test-filter = refl


-- Mégtöbb gyakorló feladat
-- splitAt függvény haskellből
-- n-edik indexnél elválasztja
-- pl splitAt 2 [4,5,6] == ([4,5] , [6])
-- Ez a feladat modellezési szempontból is érdekes
splitAt : {A : Set}{k : ℕ} → (n : ℕ) → Vec A (n + k) → (Vec A n) × (Vec A k)
splitAt = {!!}

-- Hajtogatás haskellből
-- pl foldr (+) 0 [1,2,3,4] == 1 + (2 + (3 + (4 + 0)))
foldr : {A B : Set}{n : ℕ} → (A → B → B) → B → Vec A n → B
foldr = {!!}

-- Minden elem közé beszúrunk egy elemet
-- pl intersperse 10 [1,2,3] == [1,10,2,10,3]
intersperse : {A : Set}{n : ℕ} → A → Vec A (suc n) → Vec A (suc (n * 2))
intersperse = {!!}






-- MEGOLDÁSOK
{-
splitAt zero xs = [] , xs
splitAt (suc n) (x ∷ xs) with splitAt n xs
... | l , r = (x ∷ l) , r

foldr f b [] = b
foldr f b (x ∷ xs) = f x (foldr f b xs)

intersperse a (x ∷ []) = x ∷ []
intersperse a (x ∷ y ∷ vs) = x ∷ a ∷ (intersperse a (y ∷ vs))
-}
