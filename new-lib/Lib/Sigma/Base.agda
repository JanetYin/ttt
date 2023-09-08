{-# OPTIONS --safe #-}

module Lib.Sigma.Base where

open import Lib.Sigma.Type

map : ∀{i j k l}{A : Set i}{B : A → Set j}{C : Set k}{D : C → Set l} →
  (A → C) → ({a : A} → B a → {c : C} → D c) → Σ A B → Σ C D
map f g (a , b) = f a , g b