module gy10 where

open import Lib hiding (sym; trans; cong; subst; idl+; idr+; sucr+; ass+; comm+; dist+*; nullr*; idl*; idr*; sucr*; ass*; comm*)

-- \== = ≡
{-
data _≡_ {i}{A : Set i}(a : A) : A → Set i where
  refl : a ≡ a
-}

---------------------------------------------------------
-- equality
------------------------------------------------------

sym : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq2 = eq2

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀{i j}{A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y
subst P refl px = px

symWithSubst : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
symWithSubst {i} {A} {x} {y} eq = subst P eq refl where
  P : A → Set i
  P y = y ≡ x

transWithSubst : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
transWithSubst = {!   !}

congWithSubst : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
congWithSubst = {!   !}

---------------------------------------------------------
-- properties of +,*
------------------------------------------------------

idl+ : (n : ℕ) → zero + n ≡ n
idl+ _ = refl

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
comm+-helper n m = sym (sucr+ n m)

comm+ : (m n : ℕ) → m + n ≡ n + m
comm+ zero n = sym (idr+ n)
comm+ (suc m) n = trans (cong suc (comm+ m n)) (comm+-helper n m)

-- \== = ≡; \< = ⟨; \> = ⟩
-- \qed = ∎
-- x ≡⟨ eq1 ⟩ eq2 = trans eq1 eq2

dist+* : (m n o : ℕ) → (n + o) * m ≡ n * m + o * m
dist+* m zero o = refl
dist+* m (suc n) o =
  (suc n + o) * m
  ≡⟨ refl ⟩ -- definíció szerint ugyanazok.
  m + (n + o) * m
  ≡⟨ cong (λ x → m + x) (dist+* m n o) ⟩
  m + (n * m + o * m)
  ≡⟨ sym (ass+ m (n * m) (o * m)) ⟩
  m + n * m + o * m ∎

nullr* : (n : ℕ) → n * 0 ≡ 0
nullr* = {!   !}

idl* : (n : ℕ) → 1 * n ≡ n
idl* = {!    !}

idr* : (n : ℕ) → n * 1 ≡ n
idr* = {!    !}

sucr* : (n m : ℕ) → n * suc m ≡ n + n * m
sucr* = {!    !}

ass* : (m n o : ℕ) → (m * n) * o ≡ m * (n * o)
ass* = {!   !}

comm*-helper : (n m : ℕ) → n + n * m ≡ n * suc m
comm*-helper = {!    !}

comm* : (m n : ℕ) → m * n ≡ n * m
comm* = {!    !}
