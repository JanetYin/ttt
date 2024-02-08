module gy08 where

open import Lib using (¬_ ; _↔_; _⊎_; Σ; ⊥; _,_; exfalso; inr ; inl; _×_)

--------
-- Some logic
--------

nocontra : {X : Set} → ¬ (X ↔ ¬ X)
nocontra = λ where (fst , snd) → fst (snd λ x → fst x x) (snd (λ x → fst x x))

¬¬invol₁ : {X : Set} → ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
Σ.fst ¬¬invol₁ x nx = x (λ y → y nx)
Σ.snd ¬¬invol₁ x nx = nx x

¬¬invol₂ : {X : Set} → ¬ ¬ ¬ X ↔ ¬ X
Σ.fst ¬¬invol₂ nx x = nx (λ y → y x)
Σ.snd ¬¬invol₂ x nx = nx x

nnlem : {X : Set} → ¬ ¬ (X ⊎ ¬ X)
nnlem x = x (inr (λ y → x (inl y)))

nndnp : {X : Set} → ¬ ¬ (¬ ¬ X → X)
nndnp x = x (λ y → exfalso (y (λ rx → x (λ hx → rx))))

¬∀        :    (A : Set)(P : A → Set)              → (Σ A λ a → ¬ P a)      → ¬ ((a : A) → P a)
¬∀ A P (fst , snd) y = snd (y fst)
¬Σ        :    (A : Set)(P : A → Set)              → (¬ Σ A λ a → P a)      ↔ ((a : A) → ¬ P a)
¬Σ _ _ = (λ x a y → x (a , y)) , λ where x (fst , snd) → x fst  snd


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
  not-hungarian x =  ¬ (x is-hungarian)

  not-dry-white : Set
  not-dry-white = ∀ (x : Wine) → ¬ ((x is-dry) × (x is-white))

  there-is-no-white-and-red : Set
  there-is-no-white-and-red = ∀ (x : Wine) → ¬ ((x is-white)  × (x is-red))

  every-furmint-is-white : Set
  every-furmint-is-white = ∀ (x : Wine) → x is-the-same-as furmint → x is-white

  tokaji-aszu-is-not-dry-red : Set
  tokaji-aszu-is-not-dry-red = ∀ (x : Wine) → x is-the-same-as tokaji-aszu → ¬ ((x is-dry) × (x is-red))

  _is-hungarian₂ : Wine → Set
  x is-hungarian₂ = x is-the-same-as tokaji-aszu ⊎ x is-the-same-as szekszárdi-bikavér ⊎ x is-the-same-as furmint

  there-is-foreign-wine : Set
  there-is-foreign-wine = Σ Wine λ x → not-hungarian x
















open import Lib hiding (sym; trans; cong; cong₂; subst; idl+; idr+; sucr+; ass+; comm+; dist+*; nullr*; idl*; idr*; sucr*; ass*; comm*)

---------------------------------------------------------
-- equality
------------------------------------------------------

sym : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl y = y

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀{i j}{A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y
subst P refl p = p


------

-- Only subst!

sym₂ : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym₂ x = subst (λ e → e ≡ _) x refl

trans₂ : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans₂ {x = x} y x₁ = subst (λ e → x ≡ e) x₁ y

cong₂ : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong₂ f x = subst (λ e → _ ≡ f e) x refl

-----

---------------------------------------------------------
-- properties of +,*
------------------------------------------------------

idl+ : (n : ℕ) → zero + n ≡ n
idl+ n = refl

idr+ : (n : ℕ) → n + zero ≡ n
idr+ zero = refl
idr+ (suc n) = cong suc (idr+ n)

sucr+ : (n m : ℕ) → n + suc m ≡ suc (n + m)
sucr+ zero m = refl
sucr+ (suc n) m = cong suc (sucr+ n m)

ass+ : (m n o : ℕ) → (m + n) + o ≡ m + (n + o)
ass+ zero n o = refl
ass+ (suc m) n o = cong suc (ass+ m n o)

comm+-helper : (n m : ℕ) → suc n + m ≡ n + suc m
comm+-helper zero m = refl
comm+-helper (suc n) m = cong suc (comm+-helper n m)

comm+ : (m n : ℕ) → m + n ≡ n + m
comm+ m zero = idr+ m
comm+ m (suc n) = sym (trans (cong suc (comm+ n m)) (comm+-helper m n))

dist+* : (m n o : ℕ) → (n + o) * m ≡ n * m + o * m
dist+* m zero o = refl
dist+* m (suc n) o = trans (cong (m +_) (dist+* m n o)) (sym (ass+ m (n * m) (o * m)))

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
  