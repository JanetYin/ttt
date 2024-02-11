{-# OPTIONS --safe #-}

module Lib.Maybe.Properties where

open import Lib.Maybe.Type
open import Lib.Equality.Type
open import Lib.Dec
open import Lib.Dec.PatternSynonym

just-injective : ∀{i}{A : Set i}{x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

≡-dec-Maybe : ∀{i}{A : Set i} → ((a b : A) → Dec (a ≡ b)) → (x y : Maybe A) → Dec (x ≡ y)
≡-dec-Maybe p (just x) (just y) with p x y
... | yes refl = yes refl
... | no ¬a = no λ e → ¬a (just-injective e)
≡-dec-Maybe _ (just x) nothing = no λ ()
≡-dec-Maybe _ nothing (just y) = no λ ()
≡-dec-Maybe _ nothing nothing  = yes refl