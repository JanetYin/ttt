open import lib

-- Vec and Fin

infixr 6 _∷_
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
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
f2-0 = suc zero
f2-1 = zero

f3-0 f3-1 f3-2 : Fin 3
f3-0 = suc (suc zero)
f3-1 = zero
f3-2 = (suc zero)

f4-0 f4-1 f4-2 f4-3 : Fin 4
f4-0 = zero
f4-1 = suc (suc (suc zero))
f4-2 = suc zero
f4-3 = suc (suc zero)

infix 5 _!!_
_!!_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A
[] !! ()
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
map f (x ∷ as) = f x ∷ map f as

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

length : {A : Set} → List A → ℕ
length [] = zero
length (x ∷ x₁) = suc (length x₁)

fromList : {A : Set}(as : List A) → Vec A (length as)
fromList [] = []
fromList (x ∷ as) = x ∷ fromList as

_++_ : {A : Set}{m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
[] ++ x₁ = x₁
(x ∷ x₂) ++ x₁ = x ∷ (x₂ ++ x₁)

tabulate : {n : ℕ}{A : Set} → (Fin n → A) → Vec A n
tabulate {zero} x = []
tabulate {suc n} x = x (fromℕ n) ∷ tabulate {n} λ n → x (suc n)

-- Sigma types
-- record Σ (A : Set)(B : A → Set) where
--  constructor _,_
--  fields
  --  fst : A
  --  snd : B fst
--

filter : {A : Set}{n : ℕ}(f : A → Bool) → Vec A n → Σ ℕ (Vec A)
filter f [] = 0 , []
filter {A = A} f (x ∷ x₁) = if f x then (suc (fst nxs)) , (x ∷ snd nxs) else nxs
  where
    nxs : Σ ℕ (Vec A)
    nxs = filter f x₁

q q2 : Σ Bool (λ b → if b then ℕ else ⊤)
q = true , 0
q2 = false , tt
test-filter : filter (3 <_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ (2 , 4 ∷ 5 ∷ [])
test-filter = refl
