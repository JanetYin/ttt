module gy08 where

open import Lib using (¬_ ; _↔_; _⊎_; Σ)

--------
-- Some logic
--------

nocontra : {X : Set} → ¬ (X ↔ ¬ X)
nocontra = {!!}

¬¬invol₁ : {X : Set} → ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
¬¬invol₁ = {!!}

¬¬invol₂ : {X : Set} → ¬ ¬ ¬ X ↔ ¬ X
¬¬invol₂ = {!!}

nnlem : {X : Set} → ¬ ¬ (X ⊎ ¬ X)
nnlem = {!!}

nndnp : {X : Set} → ¬ ¬ (¬ ¬ X → X)
nndnp = {!!}

¬∀        :    (A : Set)(P : A → Set)              → (Σ A λ a → ¬ P a)      → ¬ ((a : A) → P a)
¬∀ = {!!}
¬Σ        :    (A : Set)(P : A → Set)              → (¬ Σ A λ a → P a)      ↔ ((a : A) → ¬ P a)
¬Σ = {!!}


module Wine
  (Wine : Set)
  (tokaji-aszu : Wine)
  (szekszárdi-bikavér : Wine)
  (furmint : Wine)
  (bordeaux : Wine)
  (chardonnay : Wine)
  (_is-hungarian : Wine → Set)
  (_is-white : Wine → Set)
  (_is-red : Wine → Set)
  (_is-dry : Wine → Set)
  (_is-the-same-as_ : Wine → Wine → Set)
  where

  not-hungarian : Wine → Set
  not-hungarian = {!   !}

  not-dry-white : Set
  not-dry-white = {!   !}

  there-is-no-white-and-red : Set
  there-is-no-white-and-red = {!   !}

  every-furmint-is-white : Set
  every-furmint-is-white = {!   !}

  tokaji-aszu-is-not-dry-red : Set
  tokaji-aszu-is-not-dry-red = {!   !}

  _is-hungarian₂ : Set
  _is-hungarian₂ = {!   !}

  there-is-foreign-wine : Set
  there-is-foreign-wine = {!   !}
















open import Lib hiding (sym; trans; cong; cong₂; subst; idl+; idr+; sucr+; ass+; comm+; dist+*; nullr*; idl*; idr*; sucr*; ass*; comm*)

---------------------------------------------------------
-- equality
------------------------------------------------------

sym : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym = {!!}

trans : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans = {!!}

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong = {!!}

subst : ∀{i j}{A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y
subst = {!!}


------

-- Only subst!

sym₂ : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym₂ = {!   !}

trans₂ : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans₂ = {!!}

cong₂ : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong₂ = {!!}

-----

---------------------------------------------------------
-- properties of +,*
------------------------------------------------------

idl+ : (n : ℕ) → zero + n ≡ n
idl+ = {!!}

idr+ : (n : ℕ) → n + zero ≡ n
idr+ = {!!}

sucr+ : (n m : ℕ) → n + suc m ≡ suc (n + m)
sucr+ = {!!}

ass+ : (m n o : ℕ) → (m + n) + o ≡ m + (n + o)
ass+ = {!!}

comm+-helper : (n m : ℕ) → suc n + m ≡ n + suc m
comm+-helper = {!!}

comm+ : (m n : ℕ) → m + n ≡ n + m
comm+ = {!!}

dist+* : (m n o : ℕ) → (n + o) * m ≡ n * m + o * m
dist+* = {!!}

nullr* : (n : ℕ) → n * 0 ≡ 0
nullr* = {!!}

idl* : (n : ℕ) → 1 * n ≡ n
idl* = {!!}

idr* : (n : ℕ) → n * 1 ≡ n
idr* = {!!}

sucr* : (n m : ℕ) → n * suc m ≡ n + n * m
sucr* = {!!}

ass* : (m n o : ℕ) → (m * n) * o ≡ m * (n * o)
ass* = {!!}

comm*-helper : (n m : ℕ) → n + n * m ≡ n * suc m
comm*-helper = {!!}

comm* : (m n : ℕ) → m * n ≡ n * m
comm* = {!!}
