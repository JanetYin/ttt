{-# OPTIONS --safe #-}

module Lib.Maybe.Base where

open import Lib.Maybe.Type
open import Lib.Equality

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