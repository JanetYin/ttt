{-# OPTIONS --safe #-}

module Lib.Nat.Base where

open import Lib.Nat.Literals
open import Lib.Nat.Type
open import Lib.Unit
open import Lib.Empty
open import Lib.Sigma.Type
open import Lib.Sum.Type
open import Lib.Equality
open import Lib.Nat.Equality.Base
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
suc n ! = suc n * n !

case-ℕ : ∀{i}{A : Set i} → ℕ → A → A → A
case-ℕ zero    z s = z
case-ℕ (suc _) z s = s

rec-ℕ : ∀{i}{A : Set i} → ℕ → A → (A → A) → A
rec-ℕ zero    a f = a
rec-ℕ (suc n) a f = f (rec-ℕ n a f)

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