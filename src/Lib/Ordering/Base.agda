{-# OPTIONS --safe #-}

module Lib.Ordering.Base where

open import Lib.Ordering.Type
open import Lib.Equality.Type

case-Ordering : ∀{i}{A : Set i} → Ordering → A → A → A → A
case-Ordering LT a b c = a
case-Ordering EQ a b c = b
case-Ordering GT a b c = c

elim-Ordering : ∀{i}{A : Ordering → Set i} → (b : Ordering) → A LT → A EQ → A GT → A b
elim-Ordering LT a b c = a
elim-Ordering EQ a b c = b
elim-Ordering GT a b c = c

ind-Ordering : ∀{i}{A : Ordering → Set i} → (b : Ordering) → (b ≡ LT → A b) → (b ≡ EQ → A b) → (b ≡ GT → A b) → A b
ind-Ordering LT a b c = a refl
ind-Ordering EQ a b c = b refl
ind-Ordering GT a b c = c refl