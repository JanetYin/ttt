{-# OPTIONS --safe #-}

module Lib.Nat.Base where

open import Lib.Nat.Literals
open import Lib.Nat.Type
open import Lib.Unit.Type
open import Lib.Empty.Type
open import Lib.Sigma.Type
open import Lib.Sum.Type
open import Lib.Equality
open import Lib.Containers.List.Type
open import Lib.Nat.Equality.Base
open import Lib.UnitOrEmpty.Type
open import Agda.Builtin.Nat public
  hiding (Nat ; suc ; zero)
  renaming (_<_ to _<ᵇ_ ; _==_ to _==ᵇ_ ; _-_ to _-'_)

pred' : ℕ → ℕ
pred' 0 = 0
pred' (suc n) = n

pred : (n : ℕ) → .⦃ nonZero : IsNotZero n ⦄ → ℕ
pred (suc n) = n

infixr 6 _-_
_-_ : (x y : ℕ) → .⦃ nonZero : x ≥ℕ y ⦄ → ℕ
zero - zero = zero
suc x - zero = suc x
suc x - suc y = x - y

infixr 8 _^_
_^_ : ℕ → ℕ → ℕ
x ^ zero  = 1
x ^ suc n = x * x ^ n

infixl 50 _!
_! : ℕ → ℕ
zero  ! = 1
suc n ! = n ! * suc n

infixl 7 _div_
_div_ : ℕ → ℕ → ℕ
n div 1+m = div-helper 0 1+m n 1+m

infixl 7 _mod_
_mod_ : ℕ → ℕ → ℕ
n mod 1+m = mod-helper 0 1+m n 1+m

digits : ℕ → List ℕ
digits 0 = 0 ∷ []
digits n@(suc _) = digitsWithFuel n n [] where
  digitsWithFuel : ℕ → ℕ → List ℕ → List ℕ
  digitsWithFuel fuel zero acc = acc
  digitsWithFuel zero n@(suc _) acc = []
  digitsWithFuel (suc fuel) n@(suc _) acc = digitsWithFuel fuel (n div 9) (n mod 9 ∷ acc)

Evenᵗ : ℕ → ⊤or⊥
Evenᵗ 0 = ⊤ , inl refl
Evenᵗ 1 = ⊥ , inr refl
Evenᵗ (suc (suc n)) = Evenᵗ n

Even : ℕ → Set
Even n = fst (Evenᵗ n)

Oddᵗ : ℕ → ⊤or⊥
Oddᵗ 0 = ⊥ , inr refl
Oddᵗ 1 = ⊤ , inl refl
Oddᵗ (suc (suc n)) = Oddᵗ n

Odd : ℕ → Set
Odd n = fst (Oddᵗ n)

case-ℕ : ∀{i}{A : Set i} → ℕ → A → A → A
case-ℕ zero    z s = z
case-ℕ (suc _) z s = s

ite-ℕ : ∀{i}{A : Set i} → ℕ → A → (A → A) → A
ite-ℕ zero z s = z
ite-ℕ (suc n) z s = s (ite-ℕ n z s)

rec-ℕ : ∀{i}{A : Set i} → ℕ → A → (ℕ → A → A) → A
rec-ℕ zero    z s = z
rec-ℕ (suc n) z s = s n (rec-ℕ n z s)

elim-ℕ : ∀{i}{A : ℕ → Set i} → (n : ℕ) → A 0 → ({k : ℕ} → A k → A (suc k)) → A n
elim-ℕ         zero    a0 f = a0
elim-ℕ {A = A} (suc n) a0 f = f (elim-ℕ {A = A} n a0 f)

ind-ℕ : ∀{i}{A : ℕ → Set i}(n : ℕ) → ({k : ℕ} → k ≡ 0 → A 0) → ({m k : ℕ} → m ≡ suc k → A k → A (suc k)) → A n
ind-ℕ {A = A} zero    a0 ak = a0 refl
ind-ℕ {A = A} (suc n) a0 ak = ak refl (ind-ℕ {A = A} n a0 ak)

minMax : (n k : ℕ) → Σ (ℕ × ℕ) (λ {(a , b) → (n ≤ℕ k × n ≡ℕ a × k ≡ℕ b) ⊎ (k ≤ℕ n × k ≡ℕ a × n ≡ℕ b)})
minMax zero k = (zero , k) , inl (tt , tt , reflℕ k)
minMax (suc n) zero = (zero , suc n) , inr (tt , tt , reflℕ n)
minMax (suc n) (suc k) = let ((a , b) , c) = minMax n k in (suc a , suc b) , c

min : ℕ → ℕ → ℕ
min n m = fst (fst (minMax n m))

max : ℕ → ℕ → ℕ
max n m = snd (fst (minMax n m))
