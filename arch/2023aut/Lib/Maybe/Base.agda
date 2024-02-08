{-# OPTIONS --safe #-}

module Lib.Maybe.Base where

open import Lib.Maybe.Type
open import Lib.Sigma.Type
open import Lib.Sum.Type
open import Lib.Unit.Type
open import Lib.Empty.Type
open import Lib.Equality

IsJustᵗ : ∀{i}{A : Set i} → Maybe A → Σ Set (λ B → B ≡ ⊤ ⊎ B ≡ ⊥)
IsJustᵗ (just x) = ⊤ , inl refl
IsJustᵗ nothing = ⊥ , inr refl

IsJust : ∀{i}{A : Set i} → Maybe A → Set
IsJust n = fst (IsJustᵗ n)

IsNothingᵗ : ∀{i}{A : Set i} → Maybe A → Σ Set (λ B → B ≡ ⊤ ⊎ B ≡ ⊥)
IsNothingᵗ (just x) = ⊥ , inr refl
IsNothingᵗ nothing = ⊤ , inl refl

IsNothing : ∀{i}{A : Set i} → Maybe A → Set
IsNothing n = fst (IsNothingᵗ n)

elim-Maybe : ∀{a b}{A : Set a}{B : Maybe A → Set b} →
        ((x : A) → B (just x)) → B nothing → (x : Maybe A) → B x
elim-Maybe j n (just x) = j x
elim-Maybe j n nothing  = n

rec-Maybe : ∀{a b}{A : Set a}{B : Set b} → (A → B) → B → Maybe A → B
rec-Maybe = elim-Maybe

fromMaybe : ∀{a}{A : Set a} → A → Maybe A → A
fromMaybe = rec-Maybe (λ x → x)

ind-Maybe : ∀{a b}{A : Set a}{B : Maybe A → Set b} →
        ({y : Maybe A}(x : A) → y ≡ just x → B (just x)) →
        ({y : Maybe A} → y ≡ nothing → B nothing) → (x : Maybe A) → B x
ind-Maybe j n (just x) = j x refl
ind-Maybe j n nothing = n refl