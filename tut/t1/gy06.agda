module tut.t1.gy06 where

open import lib
open import Agda.Primitive

-- Mi a típusa az alábbiaknak?
-- ℕ × Bool    : Set
-- Set         : Set₁
-- Bool → Set  : Set₁
-- Set₁ ⊎ Set₂ : Set₂
-- Set → Bool  : Set₁

-- universe polymorphism
opid : ∀{i}{A : Set i} → A → A
opid x = x

-- kumulativitás ugyan nincs, de ezt lehet
record ↑ {i} (A : Set i) : Set (lsuc i) where
  constructor ↑[_]↑ 
  field
    ↓[_]↓ : A
open ↑ public

-- Mi a típusa ennek?
-- ∀{i}{A : Set i} → A → A

-- elsőrendű logika
-- A halmaz, P és Q A-n értelmezett predikátumok
-- ∀a.(P(a) ∧ Q(a)) ⊃ ∀a.P(a) ∧ ∀a.Q(a)
e1 : {A : Set} {P Q : A → Set} → ((a : A) → P a × Q a) → ((a : A) → P a) × ((a : A) → Q a) 
e1 t = (λ a → proj₁ (t a)) , λ a → proj₂ (t a)

-- (∀a.P(a) ∧ ∀a.Q(a) ⊃ ∀a.(P(a) ∧ Q(a))
e2 : {A : Set} {P Q : A → Set} → ((a : A) → P a) × ((a : A) → Q a) → ((a : A) → P a × Q a)
e2 t = λ a → proj₁ t a , proj₂ t a

-- ∀a.(P(a) ⊃ Q(a)) ⊃ ∀a.P(a) ⊃ ∀a.Q(a)
e3 : {A : Set}{P Q : A → Set} → ((a : A) → P a → Q a) → ((a : A) → P a) → (a : A) → Q a
e3 t u a = t a (u a)

-- vektor
_^_ : Set → ℕ → Set
A ^ n = rec ⊤ (λ u → A × u) n

Vec' : (A : Set)(n : ℕ) → Set
Vec' A n = A ^ n

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just : A → Maybe A

is0 : ℕ → Bool
is0 = rec true (λ _ → false)

-- head (3 , 2 , tt) = 3
head : {A : Set}{n : ℕ} → Vec' A n → Maybe A
head {n = 0} xs = Nothing 
head {n = suc n} xs = Just (proj₁ xs)

elemOr⊤ : ℕ → Set → Set
elemOr⊤ zero S = ⊤
elemOr⊤ (suc n) S = S

head' : {A : Set}{n : ℕ} → Vec' A n → elemOr⊤ n A
head' {n = zero} xs = tt
head' {n = suc n} xs = proj₁ xs

head'' : {A : Set}{n : ℕ} → Vec' A (suc n) → A
head'' = proj₁

tail : {A : Set}{n : ℕ} → Vec' A (suc n) → Vec' A n
tail = proj₂

-- hogyan adjuk meg vektorra a rekurziót?
foldr' : ∀{n}{A B : Set} → (A → B → B) → A → Vec' A n → B
foldr' f u ls = {!!}
