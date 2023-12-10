{-# OPTIONS --safe #-}

module Lib.Nat.Equality.Properties where

open import Lib.Nat.Literals
open import Lib.Nat.Equality.Base
open import Lib.Nat.Base
open import Lib.Nat.Type
open import Lib.Unit
open import Lib.Empty
open import Lib.Sigma.Type
open import Lib.Sum.Type
open import Lib.Equality

suc-injective≡ℕ : ∀{n m} → suc n ≡ℕ suc m → n ≡ℕ m
suc-injective≡ℕ e = e

pred-injective≡ℕ : ∀{n m} → .⦃ eq1 : IsNotZero n ⦄ → .⦃ eq2 : IsNotZero m ⦄ → pred n ≡ℕ pred m → n ≡ℕ m
pred-injective≡ℕ {suc n} {suc m} e = e

0≢ℕsucn : ∀ {n} → 0 ≢ℕ suc n
0≢ℕsucn = tt

sucn≢ℕ0 : ∀ {n} → suc n ≢ℕ 0
sucn≢ℕ0 = tt

sucn≢ℕn : ∀ {n} → suc n ≢ℕ n
sucn≢ℕn {zero} = tt
sucn≢ℕn {suc n} = sucn≢ℕn {n}

n≢ℕsucn : ∀ {n} → n ≢ℕ suc n
n≢ℕsucn {zero} = tt
n≢ℕsucn {suc n} = n≢ℕsucn {n}

idr+ℕ : (n : ℕ) → n + zero ≡ℕ n
idr+ℕ zero = tt
idr+ℕ (suc n) = idr+ℕ n

sucr+ℕ : (n m : ℕ) → n + suc m ≡ℕ suc (n + m)
sucr+ℕ zero m = reflℕ m
sucr+ℕ (suc n) m = sucr+ℕ n m

ass+ℕ : (m n o : ℕ) → (m + n) + o ≡ℕ m + (n + o)
ass+ℕ zero n o = reflℕ (n + o)
ass+ℕ (suc m) n o = ass+ℕ m n o

comm+ℕ : (m n : ℕ) → m + n ≡ℕ n + m
comm+ℕ zero n = symℕ (n + 0) ((idr+ℕ n))
comm+ℕ (suc m) n = 
  suc m + n , suc (n + m) , n + suc m
  ≡ℕ⟨ congℕ suc (m + n) (comm+ℕ m n) ⟩ 
  suc n + m , n + suc m , _
  ≡ℕ⟨ symℕ (n + suc m) (sucr+ℕ n m) ⟩ 
  n + suc m ∎ℕ

{-
dist+*ℕ : (m n o : ℕ) → (m + n) * o ≡ℕ m * o + n * o
dist+*ℕ zero n o = {!   !}
dist+*ℕ (suc m) n o = {!   !}
-}
{-
dist*+ : (m n o : ℕ) → m * (n + o) ≡ m * n + m * o
dist*+ zero n o = refl
dist*+ (suc m) n o =
  n + o + m * (n + o)
  ≡⟨ ass+ n o (m * (n + o)) ⟩
  n + (o + m * (n + o)) 
  ≡⟨ cong (n +_) (comm+ o (m * (n + o))) ⟩
  n + (m * (n + o) + o)
  ≡⟨ sym (ass+ n (m * (n + o)) o) ⟩
  n + m * (n + o) + o
  ≡⟨ cong (λ x → n + x + o) (dist*+ m n o) ⟩
  n + (m * n + m * o) + o
  ≡⟨ cong (_+ o) (sym (ass+ n (m * n) (m * o))) ⟩
  n + m * n + m * o + o
  ≡⟨ ass+ (n + m * n) (m * o) o ⟩
  n + m * n + (m * o + o)
  ≡⟨ cong ((n + m * n) +_) (comm+ (m * o) o) ⟩
  n + m * n + (o + m * o) ∎
-}
{-
nullr* : (n : ℕ) → n * 0 ≡ 0
nullr* zero = refl
nullr* (suc n) = nullr* n
-}
{-
idl* : (n : ℕ) → 1 * n ≡ n
idl* = idr+ 
-}
{-
idr* : (n : ℕ) → n * 1 ≡ n
idr* zero = refl
idr* (suc n) = cong suc (idr* n)
-}
{-
sucr* : (n m : ℕ) → n * suc m ≡ n + n * m
sucr* zero m = refl
sucr* (suc n) m =
  suc (m + n * suc m)
  ≡⟨ cong suc (comm+ m (n * suc m)) ⟩
  suc (n * suc m + m)
  ≡⟨ cong (λ x → suc (x + m)) (sucr* n m) ⟩
  suc (n + n * m + m)
  ≡⟨ cong suc (ass+ n (n * m) m) ⟩
  suc (n + (n * m + m))
  ≡⟨ cong (λ x → suc (n + x)) (comm+ (n * m) m) ⟩
  suc (n + (m + n * m)) ∎
-}
{-
ass* : (m n o : ℕ) → (m * n) * o ≡ m * (n * o)
ass* zero n o = refl
ass* (suc m) n o =
  (n + m * n) * o
  ≡⟨ dist+* n (m * n) o ⟩
  n * o + m * n * o 
  ≡⟨ cong (n * o +_) (ass* m n o) ⟩
  n * o + m * (n * o) ∎
-}
{-
comm* : (m n : ℕ) → m * n ≡ n * m
comm* zero n = sym (nullr* n)
comm* (suc m) n =
  n + m * n
  ≡⟨ cong (n +_) (comm* m n) ⟩
  n + n * m
  ≡⟨ sym (sucr* n m) ⟩
  n * suc m ∎
-}
{-
nulll^' : (n : ℕ) → 1 ^' n ≡ 1
nulll^' zero = refl
nulll^' (suc n) = trans (idr+ (1 ^' n)) (nulll^' n)
-}
{-
idr^ : (a : ℕ) → a ^' 1 ≡ a
idr^ = idr*
-}
{-
dist^+ : (m n o : ℕ) → m ^' (n + o) ≡ m ^' n * m ^' o
dist^+ m zero o = sym (idr+ (m ^' o))
dist^+ m (suc n) o = trans (cong (m *_) (dist^+ m n o)) (sym (ass* m (m ^' n) (m ^' o)))
-}
{-
dist^* : (a m n : ℕ) → a ^' (m * n) ≡ (a ^' m) ^' n
dist^* a 0 n = sym (nulll^' n)
dist^* a (suc m) zero = cong (a ^'_) (nullr* m)
dist^* a (suc m) (suc n) =
  a * a ^' (n + m * suc n)
  ≡⟨ cong (a *_) (dist^+ a n (m * suc n)) ⟩
  a * (a ^' n * a ^' (m * suc n))
  ≡⟨ cong (λ x → a * (a ^' n * x)) (dist^* a m (suc n)) ⟩
  a * (a ^' n * (a ^' m * (a ^' m) ^' n))
  ≡⟨ cong (λ x → a * (a ^' n * (a ^' m * x))) (sym (dist^* a m n)) ⟩
  a * (a ^' n * (a ^' m * a ^' (m * n)))
  ≡⟨ cong (a *_) (sym (ass* (a ^' n) (a ^' m) (a ^' (m * n)))) ⟩
  a * (a ^' n * a ^' m * a ^' (m * n))
  ≡⟨ cong (λ x → a * (x * a ^' (m * n))) (comm* (a ^' n) (a ^' m)) ⟩
  a * (a ^' m * a ^' n * a ^' (m * n))
  ≡⟨ cong (a *_) (ass* (a ^' m) (a ^' n) (a ^' (m * n))) ⟩
  a * (a ^' m * (a ^' n * a ^' (m * n)))
  ≡⟨ sym (ass* a (a ^' m) (a ^' n * a ^' (m * n))) ⟩
  a * a ^' m * (a ^' n * a ^' (m * n))
  ≡⟨ cong (a * a ^' m *_) (sym (dist^+ a n (m * n))) ⟩
  a * a ^' m * a ^' (n + m * n)
  ≡⟨ cong (a ^' suc m *_) (dist^* a (suc m) n) ⟩
  a ^' suc m * (a ^' suc m) ^' n ∎
-}
{-
dist*^ : (a b n : ℕ) → (a * b) ^' n ≡ a ^' n * b ^' n
dist*^ a b zero = refl
dist*^ a b (suc n) =
  a * b * (a * b) ^' n
  ≡⟨ cong (a * b *_) (dist*^ a b n) ⟩
  a * b * (a ^' n * b ^' n)
  ≡⟨ ass* a b (a ^' n * b ^' n) ⟩
  a * (b * (a ^' n * b ^' n))
  ≡⟨ cong (a *_) (sym (ass* b (a ^' n) (b ^' n))) ⟩
  a * (b * a ^' n * b ^' n)
  ≡⟨ cong (λ x → a * (x * b ^' n)) (comm* b (a ^' n)) ⟩
  a * (a ^' n * b * b ^' n)
  ≡⟨ cong (a *_) (ass* (a ^' n) b (b ^' n)) ⟩
  a * (a ^' n * (b * b ^' n))
  ≡⟨ sym (ass* a (a ^' n) (b * b ^' n)) ⟩
  a * a ^' n * (b * b ^' n) ∎
-}
{-
infix 4 _ℕ≟_
_ℕ≟_ : DecidableEquality ℕ
_ℕ≟_ zero zero = yes refl
_ℕ≟_ zero (suc y) = no (λ ())
_ℕ≟_ (suc x) zero = no (λ ())
_ℕ≟_ (suc x) (suc y) with _ℕ≟_ x y
... | yes refl = yes refl
... | no p = no λ a → p (suc-injective a)
-}