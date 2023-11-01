open import Lib hiding (fromℕ ; _-_)
open import Lib.Containers.Vector hiding (head; tail; map; length; _++_)
open import Lib.Containers.List hiding (head; tail; map; length; _++_; filter)


f : (b : Bool) → if b then ℕ else Bool
f false = true
f true = 341312

_≤_ : ℕ → ℕ → Bool
zero ≤ zero = true
zero ≤ suc y = true
suc x ≤ zero = false
suc x ≤ suc y = x ≤ y

Bool→Set : Bool → Set
Bool→Set false = ⊥
Bool→Set true = ⊤

_-_ : (n : ℕ) → (k : ℕ) → Bool→Set (k ≤ n) → ℕ
(zero - zero) k≤n = zero
(zero - suc k) ()
(suc n - zero) k≤n = suc n
(suc n - suc k) k≤n = (n - k) k≤n

-- Vec and Fin
{-
infixr 5 _∷_
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)
-}
head : {A : Set}{n : ℕ} → Vec A (suc n) → A
head (x ∷ x₁) = x

tail : {A : Set}{n : ℕ} → Vec A (suc n) → Vec A n
tail (x ∷ x₁) = x₁

countDownFrom : (n : ℕ) → Vec ℕ n
countDownFrom = {!!}

test-countDownFrom : countDownFrom 3 ≡ 3 ∷ 2 ∷ 1 ∷ []
test-countDownFrom = refl

{-
data Fin : ℕ → Set where  -- Fin n = n-elemu halmaz
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)
-}
f0 : Fin 0 → ⊥
f0 ()

f1-0 f1-1 : Fin 1
f1-0 = zero
f1-1 = suc {!!}

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
fromℕ = {!!}

test-fromℕ : fromℕ 3 ≡ suc (suc (suc zero))
test-fromℕ = refl

map : {A B : Set}(f : A → B){n : ℕ} → Vec A n → Vec B n
map f as = {!!}

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
fromList (x ∷ as) = x ∷ (fromList as)

_++_ : {A : Set}{m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
_++_ = {!!}

tabulate : {n : ℕ}{A : Set} → (Fin n → A) → Vec A n
tabulate {zero} {A} x = []
tabulate {suc n} {A} f = f zero ∷ tabulate (λ x → f (suc x))


tabulate' : {n : ℕ}{A : Set} → (Fin n → A) → Vec A n -- λ { 0 -> a₁ ; 1 -> a₂ }
tabulate' {zero} {A} x = []
tabulate' {suc n} {A} f = f zero ∷ tabulate' λ finn → f (suc finn) --(λ finn → f (suc finn))

-- Sigma types

g : Σ Bool λ b → if b then ℕ else Bool
g = false , {!!}


filter : {A : Set}{n : ℕ}(f : A → Bool) → Vec A n → Σ ℕ (λ n → Vec A n)
filter f [] = zero , []
filter f (x ∷ xs) with (f x)
... | false = filter f xs
... | true =  (suc (fst (filter f xs))) , x ∷ (snd (filter f xs)) -- filter f xs

test-filter : filter {ℕ} (3 <ᵇ_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ (2 , 4 ∷ 5 ∷ [])
test-filter = refl

-- zipWith : {A B C : Set}{n : ℕ} → (A → B → C) → Vec A n → Vec B n → Vec C n
--
