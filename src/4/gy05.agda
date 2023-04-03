-- open import lib
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

data ⊥ : Set where

-- Vec and Fin

infixr 6 _∷_
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

exvec : Vec Bool 3
exvec = true ∷ (true ∷ (false ∷ []))

head : {A : Set}{n : ℕ} → Vec A (suc n) → A
head = {!!}

tail : {A : Set}{n : ℕ} → Vec A (suc n) → Vec A n
tail = {!!}

countDownFrom : (n : ℕ) → Vec ℕ n
countDownFrom = {!!}

test-countDownFrom : countDownFrom 3 ≡ 3 ∷ 2 ∷ 1 ∷ []
test-countDownFrom = refl

data Fin : ℕ → Set where  -- Fin n = n-elemu halmaz
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

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
f4-0 = {!!}
f4-1 = {!!}
f4-2 = {!!}
f4-3 = {!!}

infix 5 _!!_
_!!_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A
xs !! n = {!!}

test-!! : 3 ∷ 4 ∷ 1 ∷ [] !! (suc (suc zero)) ≡ 1
test-!! = refl

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ = {!!}

test-fromℕ : fromℕ 3 ≡ suc (suc (suc zero))
test-fromℕ = refl

map : {A B : Set}(f : A → B){n : ℕ} → Vec A n → Vec B n
map f as = {!!}

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

length : {A : Set} → List A → ℕ
length = {!!}

-- önállóan
fromList : {A : Set}(as : List A) → Vec A (length as)
fromList = {!!}

-- önállóan
_++_ : {A : Set}{m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
_++_ = {!!}

-- önállóan
tabulate : {n : ℕ}{A : Set} → (Fin n → A) → Vec A n
tabulate = {!!}

-- Sigma types

filter : {A : Set}{n : ℕ}(f : A → Bool) → Vec A n → Σ ℕ (Vec A)
filter = {!!}

test-filter : filter (3 <_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ (2 , 4 ∷ 5 ∷ [])
test-filter = refl
