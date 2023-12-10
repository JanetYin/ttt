{-# OPTIONS --safe #-}

module Lib.Nat.Equality.Base where

open import Lib.Nat.Literals
open import Lib.Nat.Type
open import Lib.Unit
open import Lib.Empty
open import Lib.Sigma.Type
open import Lib.Sum.Type
open import Lib.Equality

IsZero : ℕ → Set
IsZero 0 = ⊤
IsZero (suc _) = ⊥

IsNotZero : ℕ → Set
IsNotZero 0 = ⊥
IsNotZero (suc _) = ⊤

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

reflℕ : ∀ n → n ≡ℕ n
reflℕ zero    = tt
reflℕ (suc n) = reflℕ n

symℕ : ∀(n){m} → .(n ≡ℕ m) → m ≡ℕ n
symℕ zero  {zero}  _ = tt
symℕ (suc n) {suc m}   = symℕ n {m}

transℕ : ∀ n m k → .(n ≡ℕ m) → .(m ≡ℕ k) → n ≡ℕ k
transℕ zero zero zero e1 e2 = tt
transℕ (suc n) (suc m) (suc k) e1 e2 = transℕ n m k e1 e2

_,_,_≡ℕ⟨_⟩_ : (x y z : ℕ) → .(x ≡ℕ y) → .(y ≡ℕ z) → x ≡ℕ z
x , y , z ≡ℕ⟨ p ⟩ q = transℕ x y z p q

-- \qed = ∎
_∎ℕ : (x : ℕ) → x ≡ℕ x
_∎ℕ = reflℕ

infixr 2 _,_,_≡ℕ⟨_⟩_
infix 3 _∎ℕ

sym≢ℕ : ∀(n){m} → .(n ≢ℕ m) → m ≢ℕ n
sym≢ℕ zero    {zero}  ()
sym≢ℕ zero    {suc m} _  = tt
sym≢ℕ (suc n) {zero}  e  = tt
sym≢ℕ (suc n) {suc m} e  = sym≢ℕ n {m} e

congℕ : (f : ℕ → ℕ) → ∀(a){b} → .(a ≡ℕ b) → f a ≡ℕ f b
congℕ f zero    {zero}  e = reflℕ (f 0)
congℕ f (suc a) {suc b} e = congℕ (λ x → f (suc x)) a {b} e

substℕ : ∀{i}(P : ℕ → Set i){x y : ℕ} → .(x ≡ℕ y) → P x → P y
substℕ P {zero} {zero} e px = px
substℕ P {suc x} {suc y} = substℕ (λ z → P (suc z)) {x} {y}

≡→≡ℕ : ∀{a b} → a ≡ b → a ≡ℕ b
≡→≡ℕ {a} refl = reflℕ a

≡ℕ→≡ : ∀{a b} → .(a ≡ℕ b) → a ≡ b
≡ℕ→≡ {zero} {zero} _ = refl
≡ℕ→≡ {zero} {suc b} ()
≡ℕ→≡ {suc a} {zero} ()
≡ℕ→≡ {suc a} {suc b} e = cong suc (≡ℕ→≡ {a} {b} e)