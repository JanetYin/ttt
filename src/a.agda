{-# OPTIONS --safe #-}
open import Lib
--open import Preloaded
record _⇔_ (A B : Set) : Set where
  constructor Bijection
  field
    to      : A → B
    from    : B → A
    to∘from : ∀ x → to (from x) ≡ x
    from∘to : ∀ x → from (to x) ≡ x
data Painfulℕ : Set where
  pain : ∀ zero? → (zero? ≡ false → Painfulℕ) → Painfulℕ
  
module PainfulNat 
  (fun-ext : ∀ {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g) where



pzero : Painfulℕ
pzero = pain true λ {()}

psuc : Painfulℕ → Painfulℕ
psuc n = pain false (λ x → n)

_p+_ : Painfulℕ → Painfulℕ → Painfulℕ
m p+ n = {!   !}

+-passoc : ∀ m n p → (m p+ n) p+ p ≡ m p+ (n p+ p)
+-passoc m n p = {!   !}

-- Maybe you'll find this helpful
pzero-same : ∀ {p} → pzero ≡ pain true p
pzero-same {p}  = cong (pain true) {! !}
  

+-pzero : ∀ n → n p+ pzero ≡ n
+-pzero n = {!   !}

+-psuc : ∀ m n → m p+ psuc n ≡ psuc (m p+ n)
+-psuc m n = {!   !}

+-pcomm : ∀ m n → m p+ n ≡ n p+ m
+-pcomm m n = {!   !}

pain⇔ℕ : Painfulℕ ⇔ ℕ
_⇔_.to pain⇔ℕ = {!   !}
_⇔_.from pain⇔ℕ = {!   !}
_⇔_.to∘from pain⇔ℕ = {!   !}
_⇔_.from∘to pain⇔ℕ = {!   !}