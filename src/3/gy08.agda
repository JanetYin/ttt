module gy08 where

open import Lib hiding (sym; trans; cong; subst; idl+; sucr+; comm+; dist+*; nullr*; idl*; idr*; sucr*; ass*; comm*)

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
subst P refl x = x

sym' : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym' x = subst (λ e → e ≡ _) x refl

trans' : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans' {x = x} {y = y} {z = z} h = subst (λ e → e ≡ z → x ≡ z) h id

cong' : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong' f x = subst (λ l → _ ≡ f l) x refl

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
comm+ zero n = sym (idr+ n)
comm+ (suc m) n = trans (comm+-helper m n) (trans (comm+ m (suc n)) (comm+-helper n m))

dist+* : (m n o : ℕ) → (n + o) * m ≡ n * m + o * m
dist+* m zero o = o * m ∎
dist+* m (suc n) o = 
    m + (n + o) * m 
    ≡⟨ cong (m +_) 
        (dist+* m n o) ⟩
    sym (ass+ m (n * m) (o * m))

nullr* : (n : ℕ) → n * 0 ≡ 0
nullr* zero = refl
nullr* (suc n) = nullr* n

idl* : (n : ℕ) → 1 * n ≡ n
idl* n = idr+ n

idr* : (n : ℕ) → n * 1 ≡ n
idr* zero = refl
idr* (suc n) = cong suc (idr* n)

sucr* : (n m : ℕ) → n * suc m ≡ n + n * m
sucr* = {!!}

ass* : (m n o : ℕ) → (m * n) * o ≡ m * (n * o)
ass* = {!!}

comm*-helper : (n m : ℕ) → n + n * m ≡ n * suc m
comm*-helper = {!!}

comm* : (m n : ℕ) → m * n ≡ n * m
comm* = {!!}
