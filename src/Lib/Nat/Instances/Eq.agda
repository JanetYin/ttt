{-# OPTIONS --safe #-}

module Lib.Nat.Instances.Eq where

open import Lib.Class.Eq
open import Lib.Nat.Type
open import Lib.Nat.Properties
open import Lib.Sigma.Type
open import Lib.Maybe.Type
open import Lib.Maybe.Base
open import Lib.Equality.Type
open import Lib.Equality.Base
open import Lib.Unit.Type
open import Lib.Empty.Type

instance
  Eqℕ : Eq ℕ
  (Eqℕ Eq.≡ᵗ zero) zero = just refl , ⊤ , refl
  (Eqℕ Eq.≡ᵗ zero) (suc b) = nothing , ⊥ , refl
  (Eqℕ Eq.≡ᵗ suc a) zero = nothing , ⊥ , refl
  (Eqℕ Eq.≡ᵗ suc a) (suc b) with (Eqℕ Eq.≡ᵗ a) b
  ... | just x , _ = just (cong suc x) , ⊤ , refl
  ... | nothing , _ = nothing , ⊥ , refl
  Eq.eqIsJust Eqℕ {zero} {zero} e = tt
  Eq.eqIsJust Eqℕ {suc a} {suc b} e with (Eqℕ Eq.≡ᵗ a) b in eq1
  ... | just x , _ = tt
  ... | nothing , _ = cast (cong (λ x → IsJust (fst x)) eq1) (eqIsJust ⦃ Eqℕ ⦄ (suc-injective e))