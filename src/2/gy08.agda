module gy08 where

open import Lib hiding (sym; trans; cong; subst; idl+; idr+; sucr+; ass+; comm+; dist+*; nullr*; idl*; idr*; sucr*; ass*; comm*)

---------------------------------------------------------
-- equality
------------------------------------------------------

sym : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl b = b

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀{i j}{A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y
subst P refl b = b

sym' : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym' a = subst (λ h → h ≡ _) a refl

trans' : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans' a = subst (λ h → h ≡ _ → _) a id

cong' : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong' f a = subst (λ h → _ ≡ f h) a refl

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
