# Függő típusok

```agda
open import Lib hiding (fromℕ)
open import Lib.Containers.Vector hiding (head; tail; map; length; _++_)
open import Lib.Containers.List hiding (head; tail; map; length; _++_; filter)
```
## Vec and Fin

```plaintext

infixr 5 _∷_
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

```

```agda

head : {A : Set}{n : ℕ} → Vec A (suc n) → A
head = {!!}

tail : {A : Set}{n : ℕ} → Vec A (suc n) → Vec A n
tail = {!!}

countDownFrom : (n : ℕ) → Vec ℕ n
countDownFrom = {!!}

test-countDownFrom : countDownFrom 3 ≡ 3 ∷ 2 ∷ 1 ∷ []
test-countDownFrom = refl

```

```plaintext

data Fin : ℕ → Set where  -- Fin n = n-elemu halmaz
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

```

```agda

f0 : Fin 0 → ⊥
f0 ()

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

```

> Lib-ben a unicode ‼ az indexelés.

```agda

infixl 9 _!!_
_!!_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A
xs !! n = {!!}

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

```

```plaintext

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

```

```agda

length : {A : Set} → List A → ℕ
length = {!!}

fromList : {A : Set}(as : List A) → Vec A (length as)
fromList = {!!}

_++_ : {A : Set}{m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
_++_ = {!!}

tabulate : {n : ℕ}{A : Set} → (Fin n → A) → Vec A n
tabulate = {!!}

```

## Sigma típus

```agda

filter : {A : Set}{n : ℕ}(f : A → Bool) → Vec A n → Σ ℕ (Vec A)
filter = {!!}

test-filter : filter {ℕ} (3 <ᵇ_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ (2 , 4 ∷ 5 ∷ [])
test-filter = refl

```
