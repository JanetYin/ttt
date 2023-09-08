{-# OPTIONS --safe #-}

module Lib.Maybe.Properties where

open import Lib.Maybe.Type
open import Lib.Equality.Type
open import Lib.Dec

just-injective : ∀{i}{A : Set i}{x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

≡-dec-Maybe : ∀{i}{A : Set i} → (x y : Maybe A) → ((a b : A) → Dec (a ≡ b)) → Dec (x ≡ y)
≡-dec-Maybe (just x) (just y) p with p x y
... | yes refl = yes refl
... | no ¬a = no λ e → ¬a (just-injective e)
≡-dec-Maybe (just x) nothing p = no λ ()
≡-dec-Maybe nothing (just y) p = no λ ()
≡-dec-Maybe nothing nothing p = yes refl