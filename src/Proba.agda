module Proba where

open import Lib

open import Lib.Containers.List

elem : ∀{i}{A : Set i} → ⦃ inst : Eq A ⦄ → A → List A → Bool
elem _ [] = false
elem a (x ∷ xs) = (a == x) ∨ elem a xs
