module gy09 where

open import Lib hiding (sym; trans; cong; subst; idl+; idr+; sucr+; ass+; comm+; dist+*; nullr*; idl*; idr*; sucr*; ass*; comm*)

---------------------------------------------------------
-- equality
------------------------------------------------------

{-
data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a
-}

sym : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl e = e

{-
other notions of trans:
_◾_ = \sq5

\< = ⟨ ; \> = ⟩ ; \qed = ∎
_≡⟨_⟩_ + _∎

_≡⟨_⟩_
Λ  Λ ^-- proof
|  |
|  ⌞ proof
value

_∎ = basically reflexivity proof with an explicit value

Usual way of using this notion:

value1
  ≡⟨ proof1 ⟩
value2
  ≡⟨ proof2 ⟩
value3
  ≡⟨ proof3 ⟩
value4 ∎
-}

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

{-
alma : ∀{i j}{A : Set i}{B : Set j}(f g : A → B){x y : A} → f x ≡ f y → x ≡ y
alma f g refl = {!!} -- fordítási hiba refl-re illeszteni.
-}

subst : ∀{i j}{A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y
subst P refl px = px

---------------------------------------------------------
-- properties of +,*
---------------------------------------------------------

idl+ : (n : ℕ) → zero + n ≡ n
idl+ n = refl

idr+ : (n : ℕ) → n + zero ≡ n
idr+ zero = refl
idr+ (suc n) = let ih = idr+ n in cong suc ih

sucr+ : (n m : ℕ) → n + suc m ≡ suc (n + m)
sucr+ zero m = refl
sucr+ (suc n) m = let ih = sucr+ n m in cong suc ih

ass+ : (m n o : ℕ) → (m + n) + o ≡ m + (n + o)
ass+ = {!!}

comm+-helper : (n m : ℕ) → suc n + m ≡ n + suc m
comm+-helper n m = sym (sucr+ n m)

comm+ : (m n : ℕ) → m + n ≡ n + m
comm+ zero n = sym (idr+ n)
comm+ (suc m) n = let ih = comm+ m n in trans (cong suc ih) (comm+-helper n m)

comm+' : (m n : ℕ) → m + n ≡ n + m
comm+' zero n = sym (idr+ n)
comm+' (suc m) n = let ih = comm+' m n in
  cong suc ih ◾ comm+-helper n m

comm+'' : (m n : ℕ) → m + n ≡ n + m
comm+'' zero n = sym (idr+ n)
comm+'' (suc m) n = let ih = comm+'' m n in
  suc (m + n)
  ≡⟨ cong suc ih ⟩
  suc (n + m)
  ≡⟨ comm+-helper n m ⟩
  n + suc m ∎

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
