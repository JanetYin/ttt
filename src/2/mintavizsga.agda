-- BEGIN FIX
{-# OPTIONS --guardedness #-}

open import Agda.Primitive

open import Agda.Builtin.Nat
  renaming (Nat to ℕ)
  public
open import Agda.Primitive
Type = Set
open import Agda.Builtin.Equality
  public
open import Agda.Builtin.Bool
  public
open import Agda.Builtin.Sigma
  public

infixr 5 _∷_
infixr 2 _×_
infixr 1 _⊎_
infix 0 _↔_

if_then_else_ : ∀{i}{A : Set i}(t : Bool)(u v : A) → A
if true  then u else v = u
if false then u else v = v

-- Product types
_×_ : ∀{ℓ κ} → Set ℓ → Set κ → Set (ℓ ⊔ κ)
A × B = Σ A λ _ → B

-- Sum types
data _⊎_ {i}{j}(A : Set i)(B : Set j) : Set (i ⊔ j) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

case : ∀ {i j k}{A : Set i}{B : Set j}{C : Set k}
         (t : A ⊎ B)(u : A → C)(v : B → C) → C
case (inl t) u v = u t
case (inr t) u v = v t

-- Empty type
data ⊥ : Set where

exfalso : ∀{i}{A : Set i} → ⊥ → A
exfalso ()

-- Unit type
record ⊤ : Set where
  constructor tt
open ⊤ public

_↔_ : ∀{i j} → Set i → Set j → Set (i ⊔ j)
A ↔ B = (A → B) × (B → A)

¬_ : ∀{i} → Set i → Set i
¬ A = A → ⊥

-- infinite stream
record Stream {ℓ}(A : Set ℓ) : Set ℓ where
  coinductive
  constructor mkStream
  field
    head : A
    tail : Stream A

open Stream public

-- fixed-length vectors
data Vec {ℓ}(A : Set ℓ) : ℕ → Set ℓ where
  [] : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

-- maybe type
data Maybe {ℓ}(A : Set ℓ) : Set ℓ where
  nothing : Maybe A
  just : A → Maybe A

-- Finite natural numbers
data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

-- coinductive natural numbers (nat ∪ {∞})
record ℕ∞ : Set where
  coinductive
  constructor mkCoNat
  field
    pred∞ : Maybe ℕ∞

open ℕ∞ public

sym : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀{i j}{A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y
subst P refl p = p

ass+ : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
ass+ zero    b c = refl
ass+ (suc a) b c = cong suc (ass+ a b c)

idr+ : (a : ℕ) → a + 0 ≡ a
idr+ zero    = refl
idr+ (suc a) = cong suc (idr+ a)

+suc : (a b : ℕ) → suc a + b ≡ a + suc b
+suc zero    b = refl
+suc (suc a) b = cong suc (+suc a b)

comm+ : (a b : ℕ) → a + b ≡ b + a
comm+ zero b = sym (idr+ b)
comm+ (suc a) b = trans (cong suc (comm+ a b)) (+suc b a)

_≤_ : ℕ → ℕ → Set
x ≤ y = Σ ℕ λ m → m + x ≡ y

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

infix  3 _∎
infixr 2 _≡⟨_⟩_

_≡⟨_⟩_ : ∀{i}{A : Set i}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

_∎ : ∀{i}{A : Set i}(a : A) → a ≡ a
a ∎ = refl

takeStream : ∀{ℓ}{A : Set ℓ}(n : ℕ) → Stream A → Vec A n
takeStream zero x = []
takeStream (suc n) x = (head x) ∷ (takeStream n (tail x))

dropStream : ∀{ℓ}{A : Set ℓ}(n : ℕ) → Stream A → Stream A
dropStream zero x = x
dropStream (suc n) x = dropStream n (tail x)

mapStream : ∀{ℓ κ}{A : Set ℓ}{B : Set κ} → (A → B) → Stream A → Stream B
head (mapStream f sa) = f (head sa)
tail (mapStream f sa) = mapStream f (tail sa)

iterate : ∀{ℓ}{A : Set ℓ} → (A → A) → A → Stream A
head (iterate f a) = a
tail (iterate f a) = iterate f (f a)

∞ : ℕ∞
pred∞ ∞ = just ∞

-- BEGIN FIX
-- b1 and b2 should be such that b1 ℕ 1 2 ≠ b2 ℕ 1 2
b1 b2 : (A : Set) → A → A → A
-- END FIX
b1 A x x₁ = x
b2 A x y = y
-- BEGIN FIX
test-b1-b2 : ¬ (b1 ℕ 1 2 ≡ b2 ℕ 1 2)
test-b1-b2 ()
-- END FIX

-- BEGIN FIX
weirdLogicalEquiv : (A B C : Set) → (B → A → (⊥ ⊎ C)) ↔ (A → (B → C × A))
-- END FIX
fst (weirdLogicalEquiv A B C) x x₁ x₂ = case (x x₂ x₁) (λ x₃ → exfalso x₃ , x₁) λ x₃ → x₃ , x₁
snd (weirdLogicalEquiv A B C) x x₁ x₂ = inr (fst (x x₂ x₁))

-- BEGIN FIX
cocΣ : (A : Set)(B : A → Set) → Σ A B ↔ ((C : Set) → ((a : A) → B a → C) → C)
-- END FIX
fst (cocΣ A B) x C x₁ = x₁ (fst x) (snd x)
snd (cocΣ A B) x = x (Σ A B) (λ a x₁ → a , x₁)

-- BEGIN FIX
prop : {P : Set} → P ⊎ ¬ P → (¬ ( ¬ P) → P)
-- END FIX
prop (inl x) x₁ = x
prop (inr x) x₁ = exfalso (x₁ x)

-- BEGIN FIX
ref≤ : (x : ℕ) → x ≤ x
-- END FIX
ref≤ x = zero , refl

-- BEGIN FIX
cong⁻¹ : {A B : Set}(a b : A)(f : A → B) → ¬ (f a ≡ f b) → ¬ (a ≡ b)
-- END FIX
cong⁻¹ a b f x x₁ = x (cong f x₁)

-- BEGIN FIX
a+b=0→a=0 : (a b : ℕ) → (a + b) ≡ 0 → a ≡ 0
-- END FIX
a+b=0→a=0 zero b x = refl

-- BEGIN FIX
noℕsqrt : ¬ ((n k : ℕ) → Σ ℕ λ m → m * m ≡ n * k)
-- END FIX
noℕsqrt x with x 1 2
... | suc (suc zero) , ()
... | suc (suc (suc n)) , ()

-- BEGIN FIX
¬¬∃↓ : ¬ ((f : ℕ → ℕ) → Σ ℕ λ n → (k : ℕ) → suc (f n) ≤ (f k))
-- END FIX
¬¬∃↓ x with x (λ _ → zero)
... | n , f with f 3
... | zero , ()
... | suc num , ()

-- BEGIN FIX
-- works like haskell's zip
zipStream : {A B : Set} → Stream A → Stream B → Stream (A × B)
-- END FIX
head (zipStream x x₁) = head x , head x₁
tail (zipStream x x₁) = zipStream (tail x) (tail x₁)
-- BEGIN FIX
test-s1 : takeStream 10 (zipStream (iterate suc 0) (iterate pred 100)) ≡
  (0 , 100) ∷ (1 , 99) ∷ (2 , 98) ∷
  (3 , 97)  ∷ (4 , 96) ∷ (5 , 95) ∷
  (6 , 94)  ∷ (7 , 93) ∷ (8 , 92) ∷
  (9 , 91) ∷ []
test-s1 = refl
test-s2 : takeStream 10 (mapStream (λ (a , b) → a + b) (zipStream (iterate (λ x → suc (suc x)) 0) (iterate pred 100))) ≡
  100 ∷ 101 ∷ 102 ∷ 103 ∷ 104 ∷ 105 ∷ 106 ∷ 107 ∷ 108 ∷ 109 ∷ []
test-s2 = refl
-- END FIX

