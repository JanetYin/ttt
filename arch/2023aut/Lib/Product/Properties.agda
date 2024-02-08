{-# OPTIONS --safe #-}

module Lib.Product.Properties where

open import Lib.Product.Type
open import Lib.Product.Base
open import Lib.Equality
open import Lib.Dec
open import Lib.Sum.Type
open import Lib.Sum.Base
open import Lib.Dec.PatternSynonym

×β₁ : ∀{i j}{A : Set i}{B : Set j}{a : A}{b : B} → fst (a , b) ≡ a
×β₁ = refl

×β₂ : ∀{i j}{A : Set i}{B : Set j}{a : A}{b : B} → snd (a , b) ≡ b
×β₂ = refl

×η : ∀{i j}{A : Set i}{B : Set j}{ab : A × B} → (fst ab , snd ab) ≡ ab
×η = refl

×≡ : ∀{i j}{A : Set i}{B : Set j}{a1 a2 : A}{b1 b2 : B} →
  (a1 , b1) ≡ (a2 , b2) ↔ a1 ≡ a2 × b1 ≡ b2
×≡ = to , from where
  to : ∀{i j}{A : Set i}{B : Set j}{a1 a2 : A}{b1 b2 : B} →
    (a1 , b1) ≡ (a2 , b2) → a1 ≡ a2 × b1 ≡ b2
  to refl = refl , refl

  from : ∀{i j}{A : Set i}{B : Set j}{a1 a2 : A}{b1 b2 : B} →
    a1 ≡ a2 × b1 ≡ b2 → (a1 , b1) ≡ (a2 , b2)
  from (refl , refl) = refl

dec× : ∀{i j}{A : Set i}{B : Set j} → Dec A → Dec B → Dec (A × B)
dec× (no ¬p) _       = no λ ab → ¬p (fst ab)
dec× (yes p) (yes q) = yes (p , q)
dec× (yes p) (no ¬q) = no λ ab → ¬q (snd ab)

instance
  DecEq× : ∀{i j}{A : Set i}{B : Set j} → ⦃ DecidableEquality A ⦄ → ⦃ DecidableEquality B ⦄ → DecidableEquality (A × B)
  DecEq× ⦃ i1 ⦄ ⦃ i2 ⦄ = DecProof λ (x1 , x2) (y1 , y2) → case (dec× (decide i1 x1 y1) (decide i2 x2 y2)) (λ e → yes (snd ×≡ e)) (λ e → no λ e2 → e (fst ×≡ e2))