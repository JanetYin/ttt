open import lib

---------------------------------------------------------
-- positivity
---------------------------------------------------------

{-# NO_POSITIVITY_CHECK #-}
data Tm : Set where
  lam : (Tm → Tm) → Tm

app : Tm → (Tm → Tm)
app (lam x) = x

self-apply : Tm
self-apply = lam (λ t → app t t)

-- C-c C-n this:
Ω : Tm
Ω = app self-apply self-apply

{-# NO_POSITIVITY_CHECK #-}
data Weird : Set where
  foo : (Weird → ⊥) → Weird

unweird : Weird → ⊥
unweird (foo x) = x (foo x)

bad : ⊥
bad = unweird (foo unweird)

-----------------------------------------
-- Vec and Fin
-----------------------------------------

infixr 6 _∷_
data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

head : {A : Set}{n : ℕ} → Vec A (suc n) → A
head (x ∷ x₁) = x

tail : {A : Set}{n : ℕ} → Vec A (suc n) → Vec A n
tail (x ∷ x₁) = x₁

countDownFrom : (n : ℕ) → Vec ℕ n
countDownFrom zero = []
countDownFrom (suc n) = suc n ∷ countDownFrom n

test-countDownFrom : countDownFrom 3 ≡ 3 ∷ 2 ∷ 1 ∷ []
test-countDownFrom = refl

data Fin : ℕ → Set where  -- Fin n = n-elemu halmaz
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

f0 : Fin 0 → ⊥
f0 ()

f1-0 : Fin 1
f1-0 = zero

f2-0 f2-1 : Fin 2
f2-0 = zero
f2-1 = suc zero

f3-0 f3-1 f3-2 : Fin 3
f3-0 = zero
f3-1 = suc zero
f3-2 = suc (suc zero)

f4-0 f4-1 f4-2 f4-3 : Fin 4
f4-0 = zero
f4-1 = suc zero
f4-2 = suc (suc zero)
f4-3 = suc (suc (suc zero))

infix 5 _!!_
_!!_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A
x ∷ xs !! zero = x
x ∷ xs !! suc n = xs !! n

test-!! : 3 ∷ 4 ∷ 1 ∷ [] !! (suc (suc zero)) ≡ 1
test-!! = refl

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero = zero
fromℕ (suc n) = suc (fromℕ n)

test-fromℕ : fromℕ 3 ≡ suc (suc (suc zero))
test-fromℕ = refl

map : {A B : Set}(f : A → B){n : ℕ} → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

length : {A : Set} → List A → ℕ
length [] = zero
length (x ∷ x₁) = suc (length x₁)

fromList : {A : Set}(as : List A) → Vec A (length as)
fromList [] = []
fromList (x ∷ xs) = x ∷ fromList xs

_++_ : {A : Set}{m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

tabulate : {n : ℕ}{A : Set} → (Fin n → A) → Vec A n
tabulate {zero} {A} f = []
tabulate {suc n} {A} f = f (fromℕ n) ∷ tabulate {n}{A} λ x → f (suc x)

-- Sigma types

filter : {A : Set}{n : ℕ}(f : A → Bool) → Vec A n → Σ ℕ (Vec A)
filter f [] = zero , []
filter f (x ∷ xs) = if (f x) then suc (fst (filter f xs)) , x ∷ snd (filter f xs) else filter f xs

test-filter : filter (3 <_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ (2 , 4 ∷ 5 ∷ [])
test-filter = refl
