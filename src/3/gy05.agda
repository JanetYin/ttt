module gy05 where

open import Lib hiding (fromℕ)
open import Lib.Containers.Vector hiding (head; tail; map; length; _++_)
open import Lib.Containers.List hiding (head; tail; map; length; _++_; filter)

f : ℕ → Set
f zero = ⊤
f (suc _) = ⊥

-- Vec and Fin
{-
infixr 5 _∷_
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)
-}
head : {A : Set}{n : ℕ} → Vec A (suc n) → A
head (x ∷ _) = x

tail : {A : Set}{n : ℕ} → Vec A (suc n) → Vec A n
tail (_ ∷ x) = x

countDownFrom : (n : ℕ) → Vec ℕ n
countDownFrom zero = []
countDownFrom m@(suc n) = m ∷ countDownFrom n

test-countDownFrom : countDownFrom 3 ≡ 3 ∷ 2 ∷ 1 ∷ []
test-countDownFrom = refl

{-
data Fin : ℕ → Set where  -- Fin n = n-elemu halmaz
  fzero : {n : ℕ} → Fin (suc n)
  fsuc  : {n : ℕ} → Fin n → Fin (suc n)
-}

f0 : Fin 0 → ⊥
f0 ()

f1-0 : Fin 1
f1-0 = fzero

f2-0 f2-1 : Fin 2
f2-0 = 0
f2-1 = fsuc fzero

f3-0 f3-1 f3-2 : Fin 3
f3-0 = fsuc (fsuc (fzero))
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
(x ∷ _) !! fzero = x
(_ ∷ xs) !! fsuc y = xs !! y

test-!! : (the ℕ 3 ∷ 4 ∷ 1 ∷ []) !! (fsuc (fsuc fzero)) ≡ 1
test-!! = refl

test2-!! : (the ℕ 3 ∷ 4 ∷ 1 ∷ 0 ∷ 10 ∷ []) !! 3 ≡ 0 -- 3-as literál a !! után valójában Fin 5 típusú.
test2-!! = refl

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero = fzero
fromℕ (suc n) = fsuc (fromℕ n)

test-fromℕ : fromℕ 3 ≡ fsuc (fsuc (fsuc fzero))
test-fromℕ = refl

map : {A B : Set}(f : A → B){n : ℕ} → Vec A n → Vec B n
map {A} {B} f {zero} as = []
map {A} {B} f {suc n} (x ∷ as) = f x ∷ map f as

{-
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A
-}

length : {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

fromList : {A : Set}(as : List A) → Vec A (length as)
fromList [] = []
fromList (x ∷ as) = x ∷ fromList as

{-
Similarly, zero refers to one of two constructors.
Due to how it does type inference, Agda does not allow overloading of defined names,
but does allow overloading of constructors.
It is recommended that one restrict overloading to related meanings, as we have done here,
but it is not required.
-}

_++_ : {A : Set}{m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
_++_ = {!!}

tabulate : {n : ℕ}{A : Set} → (Fin n → A) → Vec A n
tabulate = {!!}

test-tabulate : tabulate (the (Fin 3 -> ℕ) (λ {fzero -> 6; (fsuc fzero) -> 9; (fsuc (fsuc fzero)) -> 2}))
                  ≡ 6 ∷ 9 ∷ 2 ∷ []
test-tabulate = refl

-- Sigma types

what : Σ ℕ (Vec Bool)
what = 10 , {!!}

filter : {A : Set}{n : ℕ}(f : A → Bool) → Vec A n → Σ ℕ (Vec A)
filter = {!!}

test-filter : filter {ℕ} (3 <ᵇ_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ (2 , 4 ∷ 5 ∷ [])
test-filter = refl

---

open import Lib.Containers.CoVector as CV

n : ℕ∞
pred∞ n = just n

z : ℕ∞
pred∞ z = nothing

suc∞ : ℕ∞ → ℕ∞
pred∞ (suc∞ x) = just x

g : Set → Set₁
g x = Lift _ x

ei : ℕ∞
ei = suc∞ (suc∞ (suc∞ (suc∞ (suc∞ (suc∞ (suc∞ (suc∞ z)))))))

test : CV.CoVec ℕ∞ n
CoVec.head test = n
CoVec.tail test = test

eiv : CoVec Set ei
CoVec.head eiv = ⊤
CoVec.head (CoVec.tail eiv) = Vec Bool 1
CoVec.head (CoVec.tail (CoVec.tail eiv)) = ⊥
CoVec.head (CoVec.tail (CoVec.tail (CoVec.tail eiv))) = Bool → Bool
CoVec.head (CoVec.tail (CoVec.tail (CoVec.tail (CoVec.tail eiv)))) = ℕ
CoVec.head (CoVec.tail (CoVec.tail (CoVec.tail (CoVec.tail (CoVec.tail eiv))))) = ℕ∞
CoVec.head (CoVec.tail (CoVec.tail (CoVec.tail (CoVec.tail (CoVec.tail (CoVec.tail eiv)))))) = CoVec ℕ ei
CoVec.head (CoVec.tail (CoVec.tail (CoVec.tail (CoVec.tail (CoVec.tail (CoVec.tail (CoVec.tail eiv))))))) = ⊥
CoVec.head (CoVec.tail (CoVec.tail (CoVec.tail (CoVec.tail (CoVec.tail (CoVec.tail (CoVec.tail (CoVec.tail eiv)))))))) = Fin 0
CoVec.tail (CoVec.tail (CoVec.tail (CoVec.tail (CoVec.tail (CoVec.tail (CoVec.tail (CoVec.tail (CoVec.tail eiv)))))))) {{ () }}

mapCV : {A B : Set}{n : ℕ∞}(f : A → B)(cv : CV.CoVec A n) → CV.CoVec B n
CoVec.head (mapCV f cv) = f (CV.head cv)
CoVec.tail (mapCV f cv) = mapCV f (CoVec.tail cv)
  