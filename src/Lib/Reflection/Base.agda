{-# OPTIONS --safe #-}

module Lib.Reflection.Base where

open import Lib.Unit.Type
open import Lib.Function
open import Lib.Containers.List.Type
open import Lib.Bool.Type
open import Lib.Bool.Base

open import Agda.Builtin.Reflection public
open import Agda.Builtin.String public

fmapTC : ∀{i j}{A : Set i}{B : Set j} → (A → B) → TC A → TC B
fmapTC f tc = bindTC tc (λ a → returnTC (f a))

apTC : ∀{i j}{A : Set i}{B : Set j} → TC (A → B) → TC A → TC B
apTC tcF tcA = bindTC tcF (λ f → bindTC tcA (λ a → returnTC (f a)))

liftA2TC : ∀{i j k}{A : Set i}{B : Set j}{C : Set k} → (A → B → C) → TC A → TC B → TC C
liftA2TC f tcA tcB = apTC (fmapTC f tcA) tcB

constBindTC : ∀{i j}{A : Set i}{B : Set j} → TC A → TC B → TC B
constBindTC tcA tcB = bindTC tcA (λ _ → tcB)

macro
  doesNotTypeCheck : Term → Term → String → Term → TC ⊤
  doesNotTypeCheck t₁ t₂ msg hole = let info = arg-info visible (modality relevant quantity-0) in
    bindTC
      (catchTC (bindTC (inferType (def (quote _$_) (arg info t₁ ∷ arg info t₂ ∷ []))) (λ _ → returnTC true)) (returnTC false)) (λ b →
      if b then typeError (strErr msg ∷ []) else unify hole (quoteTerm ⊤))
