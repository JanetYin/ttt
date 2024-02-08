{-# OPTIONS --safe #-}

module Lib.Equality.Properties where

open import Lib.Equality.Type
open import Lib.Equality.Base

trans-assoc : ∀{i}{A : Set i}{a b c d : A}(eq1 : a ≡ b)(eq2 : b ≡ c)(eq3 : c ≡ d) →
  trans (trans eq1 eq2) eq3 ≡ trans eq1 (trans eq2 eq3)
trans-assoc refl _ _ = refl

cong∘ : ∀{i j}{A : Set i}{B : Set j}(f : B → A)(g : A → B) →
  {a b : A}(eq : a ≡ b) → cong f (cong g eq) ≡ cong (λ x → f (g x)) eq
cong∘ f g refl = refl

cong-id : ∀{i}{A : Set i}{a b : A} →
  (eq : a ≡ b) → cong (λ x → x) eq ≡ eq
cong-id refl = refl

substconst  : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : Set ℓ'}{a a' : A}(e : a ≡ a'){b : B} →
  subst (λ _ → B) e b ≡ b
substconst refl = refl

substcong : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}(C : B → Set ℓ'')(f : A → B) → 
  {a a' : A}(e : a ≡ a'){c : C (f a)} → 
  subst {A = B} C (cong f e) c ≡ subst {A = A} (λ a → C (f a)) e c
substcong C f refl = refl

substΠ : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}(C : A → B → Set ℓ'') →
  {a a' : A}(e : a ≡ a'){f : (b : B) → C a b} → 
  subst (λ a → (b : B) → C a b) e f ≡ λ b → subst (λ a → C a b) e (f b)
substΠ C refl = refl

substsubst : ∀{ℓ}{A : Set ℓ}{ℓ'}(P : A → Set ℓ'){a a' a'' : A}(e : a ≡ a')(e' : a' ≡ a''){p : P a} →
  subst P e' (subst P e p) ≡ subst P (trans e e') p
substsubst P refl refl = refl

subst→' : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}(C : A → Set ℓ''){a a' : A}(e : a ≡ a'){f : B → C a} → 
  subst (λ a → B → C a) e f ≡ λ b → subst C e (f b)
subst→' C refl = refl

subst$ : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : A → Set ℓ'}{C : A → Set ℓ''}
  (f : ∀ a → B a → C a){a a' : A}(e : a ≡ a'){b : B a} → 
  f a' (subst B e b) ≡ subst C e (f a b) 
subst$ f refl = refl