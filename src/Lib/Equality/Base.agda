{-# OPTIONS --safe #-}

module Lib.Equality.Base where

open import Lib.Equality.Type
open import Lib.Sigma.Type
open import Lib.Sum.Type
open import Lib.Unit.Type
open import Lib.Empty.Type

sym : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans eq1 refl = eq1

-- \sq5 = ◾

infixr 2 _◾_

_◾_ : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
_◾_ = trans

{-# DISPLAY trans = _◾_ #-}

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀{i j k}{A : Set i}{B : Set j}{C : Set k}(f : A → B → C){x x' : A}{y y' : B} →
  x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

cong₃ : ∀{i j k l}{A : Set i}{B : Set j}{C : Set k}{D : Set l}(f : A → B → C → D){x x' : A}{y y' : B}{z z' : C} →
  x ≡ x' → y ≡ y' → z ≡ z' → f x y z ≡ f x' y' z'
cong₃ f refl refl refl = refl

subst : ∀{i j}{A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y
subst P refl px = px

subst₂ : ∀{i j k}{A : Set i}{B : Set j}(P : A → B → Set k){x x' : A}{y y' : B} → x ≡ x' → y ≡ y' → P x y → P x' y'
subst₂ P {x} {x'} {y} e1 e2 pxy = subst (P x') e2 (subst (λ x → P x y) e1 pxy)

subst₃ : ∀{i j k l}{A : Set i}{B : Set j}{C : Set k}(P : A → B → C → Set l){x x' : A}{y y' : B}{z z' : C}
       → x ≡ x' → y ≡ y' → z ≡ z' → P x y z → P x' y' z'
subst₃ P {x} {x'} {y} {y'} {z} e1 e2 e3 pxyz = subst (P x' y') e3 (subst (λ y → P x' y z) e2 (subst (λ x → P x y z) e1 pxyz))

cast : ∀{i}{A B : Set i} → A ≡ B → A → B
cast refl x = x

-- \== = ≡
-- \< = ⟨
-- \> = ⟩
_≡⟨_⟩_ : ∀{i}{A : Set i}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = trans p q

-- \qed = ∎
_∎ : ∀{i}{A : Set i}(x : A) → x ≡ x
_ ∎ = refl

infixr 2 _≡⟨_⟩_
infix 3 _∎
