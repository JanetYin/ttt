module hf10 where

open import lib

sym : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq2 = eq2

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀{i j k}{A : Set i}{B : Set j}{C : Set k}(f : A → B → C){x x' : A}{y y' : B} →
  x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

cong₃ : ∀{i j k l}{A : Set i}{B : Set j}{C : Set k}{D : Set l}(f : A → B → C → D){x x' : A}{y y' : B}{z z' : C} →
  x ≡ x' → y ≡ y' → z ≡ z' → f x y z ≡ f x' y' z'
cong₃ f refl refl refl = refl

subst : ∀{i j}{A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y
subst P refl px = px

-- \== = ≡
-- \< = ⟨
-- \> = ⟩
_≡⟨_⟩_ : ∀{i}{A : Set i}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = trans p q

-- \qed = ∎
_∎ : ∀{i}{A : Set i}(x : A) → x ≡ x
_ ∎ = refl

infixr 2 _≡⟨_⟩_
infix 3 _∎

-------------------------------------------------

idl+ : (n : ℕ) → zero + n ≡ n
idl+ n = refl

idr+ : (n : ℕ) → n + zero ≡ n
idr+ zero = refl
idr+ (suc n) = cong suc (idr+ n)

sucr+ : (n m : ℕ) → n + suc m ≡ suc (n + m)
sucr+ zero m = refl
sucr+ (suc n) m = cong (λ x → suc x) (sucr+ n m)

ass+ : (m n o : ℕ) → (m + n) + o ≡ m + (n + o)
ass+ zero n o = refl
ass+ (suc m) n o = cong suc (ass+ m n o)

comm+-helper : (n m : ℕ) → suc n + m ≡ n + suc m
comm+-helper n m = sym (sucr+ n m)

comm+ : (m n : ℕ) → m + n ≡ n + m
comm+ zero n = sym (idr+ n)
comm+ (suc m) n = trans (cong suc (comm+ m n)) (comm+-helper n m)

-------------------------------------------------

dist+* : (m n o : ℕ) → (m + n) * o ≡ m * o + n * o
dist+* = {!   !}

dist*+ : (m n o : ℕ) → m * (n + o) ≡ m * n + m * o
dist*+ = {!   !}

nulll* : (n : ℕ) → 0 * n ≡ 0
nulll* = {!   !}

nullr* : (n : ℕ) → n * 0 ≡ 0
nullr* = {!   !}

idl* : (n : ℕ) → 1 * n ≡ n
idl* = {!   !}

idr* : (n : ℕ) → n * 1 ≡ n
idr* = {!   !}

ass* : (m n o : ℕ) → (m * n) * o ≡ m * (n * o)
ass* = {!   !}

comm*-helper : (n m : ℕ) → n * suc m ≡ n + n * m
comm*-helper = {!!}

comm* : (m n : ℕ) → m * n ≡ n * m
comm* = {!!}
--------------------------------------------------------

2n : (n : ℕ) → 2 * n ≡ n + n
2n = {!   !}

2n' : (n : ℕ) → n * 2 ≡ n + n
2n' = {!   !}

very-comm : (a b c d : ℕ) → (a * b) + (c * d) ≡ (d * c) + (b * a)
very-comm = {!  !}

-- Hosszabb feladat
sumSq : (a b : ℕ) → (a + b) * (a + b) ≡ a * a + 2 * a * b + b * b
sumSq = {!   !}