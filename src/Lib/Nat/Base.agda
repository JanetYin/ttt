{-# OPTIONS --safe #-}

module Lib.Nat.Base where

open import Lib.Nat.Literals
open import Lib.Nat.Type
open import Lib.Unit
open import Lib.Empty
open import Lib.Sigma.Type
open import Lib.Sum.Type
open import Lib.Equality
open import Agda.Builtin.Nat public
  hiding (Nat ; suc ; zero)
  renaming (_<_ to _<ᵇ_ ; _==_ to _==ᵇ_ ; _-_ to _-'_)

IsZero : ℕ → Set
IsZero 0 = ⊤
IsZero (suc _) = ⊥

IsNotZero : ℕ → Set
IsNotZero 0 = ⊥
IsNotZero (suc _) = ⊤

pred' : ℕ → ℕ
pred' 0 = 0
pred' (suc n) = n

pred : (n : ℕ) → .⦃ IsNotZero n ⦄ → ℕ
pred (suc n) = n

infix 4 _≤ℕᵗ_ _<ℕᵗ_ _>ℕᵗ_ _≥ℕᵗ_ _≡ℕᵗ_ _≢ℕᵗ_ _≤ℕ_ _<ℕ_ _>ℕ_ _≥ℕ_ _≡ℕ_ _≢ℕ_

_≤ℕᵗ_ : ℕ → ℕ → Σ Set (λ A → A ≡ ⊤ ⊎ A ≡ ⊥)
zero ≤ℕᵗ _ = ⊤ , inl refl
suc x ≤ℕᵗ zero = ⊥ , inr refl
suc x ≤ℕᵗ suc y = x ≤ℕᵗ y

_≤ℕ_ : ℕ → ℕ → Set
x ≤ℕ y = fst (x ≤ℕᵗ y)

_<ℕᵗ_ : ℕ → ℕ → Σ Set (λ A → A ≡ ⊤ ⊎ A ≡ ⊥)
_ <ℕᵗ zero = ⊥ , inr refl
zero <ℕᵗ suc y = ⊤ , inl refl
suc x <ℕᵗ suc y = x <ℕᵗ y

_<ℕ_ : ℕ → ℕ → Set
x <ℕ y = fst (x <ℕᵗ y)

_>ℕᵗ_ : ℕ → ℕ → Σ Set (λ A → A ≡ ⊤ ⊎ A ≡ ⊥)
zero >ℕᵗ _ = ⊥ , inr refl
suc x >ℕᵗ zero = ⊤ , inl refl
suc x >ℕᵗ suc y = x >ℕᵗ y

_>ℕ_ : ℕ → ℕ → Set
x >ℕ y = fst (x >ℕᵗ y)

_≥ℕᵗ_ : ℕ → ℕ → Σ Set (λ A → A ≡ ⊤ ⊎ A ≡ ⊥)
_ ≥ℕᵗ zero = ⊤ , inl refl
zero ≥ℕᵗ suc y = ⊥ , inr refl
suc x ≥ℕᵗ suc y = x ≥ℕᵗ y

_≥ℕ_ : ℕ → ℕ → Set
x ≥ℕ y = fst (x ≥ℕᵗ y)

_≡ℕᵗ_ : ℕ → ℕ → Σ Set (λ A → A ≡ ⊤ ⊎ A ≡ ⊥)
zero ≡ℕᵗ zero = ⊤ , inl refl
zero ≡ℕᵗ suc y = ⊥ , inr refl
suc x ≡ℕᵗ zero = ⊥ , inr refl
suc x ≡ℕᵗ suc y = x ≡ℕᵗ y

_≡ℕ_ : ℕ → ℕ → Set
x ≡ℕ y = fst (x ≡ℕᵗ y)

_≢ℕᵗ_ : ℕ → ℕ → Σ Set (λ A → A ≡ ⊤ ⊎ A ≡ ⊥)
zero ≢ℕᵗ zero = ⊥ , inr refl
zero ≢ℕᵗ suc y = ⊤ , inl refl
suc x ≢ℕᵗ zero = ⊤ , inl refl
suc x ≢ℕᵗ suc y = x ≢ℕᵗ y

_≢ℕ_ : ℕ → ℕ → Set
x ≢ℕ y = fst (x ≢ℕᵗ y)

substℕ : ∀{i}(P : ℕ → Set i){x y : ℕ} → .(x ≡ℕ y) → P x → P y
substℕ P {zero} {zero} e px = px
substℕ P {suc x} {suc y} = substℕ (λ z → P (suc z)) {x} {y}

infixr 6 _-_
_-_ : (x y : ℕ) → .⦃ x ≥ℕ y ⦄ → ℕ
zero - zero = zero
suc x - zero = suc x
suc x - suc y = x - y

infixr 8 _^'_
_^'_ : ℕ → ℕ → ℕ
x ^' zero  = 1
x ^' suc n = x * x ^' n

infixr 8 _^_
_^_ : (x y : ℕ) → .⦃ y + x ≢ℕ 0 ⦄ → ℕ
x ^ zero = 1
x ^ suc zero = x
x ^ suc (suc y) = x * (x ^ suc y)

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
elim-ℕ zero    a0 f = a0
elim-ℕ {A = A} (suc n) a0 f = f (elim-ℕ {A = A} n a0 f)

ind-ℕ : ∀{i}{A : ℕ → Set i}(n : ℕ) → ({k : ℕ} → k ≡ 0 → A 0) → ({m k : ℕ} → m ≡ suc k → A k → A (suc k)) → A n
ind-ℕ {A = A} zero    a0 ak = a0 {0} refl
ind-ℕ {A = A} (suc n) a0 ak = ak {suc n} {n} refl (ind-ℕ {A = A} n a0 ak)