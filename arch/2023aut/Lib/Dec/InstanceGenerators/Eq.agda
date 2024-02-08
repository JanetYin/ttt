{-# OPTIONS --safe #-}

module Lib.Dec.InstanceGenerators.Eq where

open import Lib.Dec.Type
open import Lib.Dec.Base

open import Lib.Class.Eq

open import Lib.Sigma.Type

open import Lib.Sum.Base

open import Lib.Maybe.Type

open import Lib.Equality.Type

open import Lib.Unit.Type

open import Lib.Empty.Type

DecidableEquality→Eq : ∀{i}{A : Set i} → DecidableEquality A → Eq A
DecidableEquality→Eq inst = record { _≡ᵗ_ = λ a b → case (decide inst a b) (λ e → just e , ⊤ , refl) (λ e → nothing , ⊥ , refl) }
