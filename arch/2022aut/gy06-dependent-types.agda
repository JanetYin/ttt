open import lib

-- Vec and Fin

infixr 6 _∷_
data Vec (A : Type) : ℕ → Type where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

head : {A : Type}{n : ℕ} → Vec A (suc n) → A
head = {!!}

tail : {A : Type}{n : ℕ} → Vec A (suc n) → Vec A n
tail = {!!}

countDownFrom : (n : ℕ) → Vec ℕ n
countDownFrom = {!!}

test-countDownFrom : countDownFrom 3 ≡ 3 ∷ 2 ∷ 1 ∷ []
test-countDownFrom = refl

data Fin : ℕ → Type where  -- Fin n = n-elemu halmaz
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

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

infix 5 _!!_
_!!_ : {A : Type}{n : ℕ} → Vec A n → Fin n → A
xs !! n = {!!}

test-!! : 3 ∷ 4 ∷ 1 ∷ [] !! (suc (suc zero)) ≡ 1
test-!! = refl

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ = {!!}

test-fromℕ : fromℕ 3 ≡ suc (suc (suc zero))
test-fromℕ = refl

map : {A B : Type}(f : A → B){n : ℕ} → Vec A n → Vec B n
map f as = {!!}

data List (A : Type) : Type where
  []  : List A
  _∷_ : A → List A → List A

length : {A : Type} → List A → ℕ
length = {!!}

fromList : {A : Type}(as : List A) → Vec A (length as)
fromList = {!!}

_++_ : {A : Type}{m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
_++_ = {!!}

tabulate : {n : ℕ}{A : Type} → (Fin n → A) → Vec A n
tabulate = {!!}

-- Sigma types

filter : {A : Type}{n : ℕ}(f : A → Bool) → Vec A n → Σ ℕ (Vec A)
filter = {!!}

test-filter : filter (3 <_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ (2 , 4 ∷ 5 ∷ [])
test-filter = refl

Σ=⊎ : {A B : Type} → Σ Bool (if_then A else B) ↔ A ⊎ B
Σ=⊎ = {!!}

Σ=× : {A B : Type} → Σ A (λ _ → B) ↔ A × B
Σ=× = {!!}

Π=→ : {A B : Type} → ((a : A) → (λ _ → B) a) ≡ (A → B)
Π=→ = {!!}

→=× : {A B : Type} → ((b : Bool) → if b then A else B) ↔ A × B
→=× = {!!}

dependentCurry : {A : Type}{B : A → Type}{C : (a : A) → B a → Type} →
  ((a : A)(b : B a) → C a b) ↔ ((w : Σ A B) → C (fst w) (snd w))
dependentCurry = {!!}

∀×-distr  : {A : Type}{P : A → Type}{Q : A → Type} → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
∀×-distr = {!!}

Bool=Fin2 : Bool ↔ Fin 2
Bool=Fin2 = {!!}

Fin1+3=Fin4 : Fin (1 + 3) ↔ Fin 1 ⊎ Fin 3
Fin1+3=Fin4 = {!!}

-- relating Fin m ⊎ Fin n and Fin (m + n)

inj₁f : {m n : ℕ} → Fin m → Fin (m + n)
inj₁f i = {!!}

test-inj₁f : inj₁f {3}{4} (suc (suc zero)) ≡ suc (suc zero)
test-inj₁f = refl

inj₂f : {m n : ℕ} → Fin n → Fin (m + n)
inj₂f {m}  i = {!!}

test-inj₂f : inj₂f {3}{4} (suc (suc zero)) ≡ suc (suc (suc (suc (suc zero))))
test-inj₂f = refl

f : {m n : ℕ} → Fin m ⊎ Fin n → Fin (m + n)
f (inl i) = inj₁f i
f (inr i) = inj₂f i

casef : {m n : ℕ}{C : Type} → (Fin m → C) → (Fin n → C) → Fin (m + n) → C
casef {m}  f g i       = {!!}

test-casef : casef {3}{3} (λ i → i) (λ i → i) (suc (suc zero)) ≡ suc (suc zero)
test-casef = refl
test-casef' : casef {3}{3} (λ i → i) (λ i → i) (suc (suc (suc zero))) ≡ zero
test-casef' = refl
test-casef'' : casef {3}{3} (λ i → i) (λ i → i) (suc (suc (suc (suc zero)))) ≡ suc zero
test-casef'' = refl

-- use inj₁f,inj₂f in one direction and "casef inj₁ inj₂" in the other direction
Fin+ : {m n : ℕ} → Fin (m + n) ↔ Fin m ⊎ Fin n
Fin+ = {!!}

-- this might be hard
Fin* : {m n : ℕ} → Fin (m * n) ↔ Fin m × Fin n
Fin* = {!!}

-- n-1
--  Σ  a i = a 0 + a 1 + ... + a (n-1)
-- i=0

Σℕ : (n : ℕ) → (Fin n → ℕ) → ℕ
Σℕ zero    a = 0
Σℕ (suc n) a = a zero + Σℕ n (λ i → a (suc i))

-- not very easy
Σ+ : (n : ℕ)(a : Fin n → ℕ) → Σ (Fin n) (λ i → Fin (a i)) ↔ Fin (Σℕ n a)
Σ+ = {!!}

-- n-1
--  Π  a i = a 0 * a 1 * ... * a (n-1)
-- i=0

Πℕ : (n : ℕ) → (Fin n → ℕ) → ℕ
Πℕ zero    a = 0
Πℕ (suc n) a = a zero * Πℕ n (λ i → a (suc i))

-- not very easy
Π* : (n : ℕ)(a : Fin n → ℕ) → ((i : Fin n) → Fin (a i)) ↔ Fin (Πℕ n a)
Π* = {!!}
