{-# OPTIONS --safe #-}

module Lib.Containers.Vector.Properties where

open import Lib.Containers.Vector.Type
open import Lib.Containers.Vector.Base
open import Lib.Sigma hiding (map)
open import Lib.Equality
open import Lib.Dec
open import Lib.Nat
open import Lib.Unit
open import Lib.Empty

∷-injectiveˡ : ∀{i}{A : Set i}{n : ℕ}{x y : A}{xs ys : Vec A n} → 
  x ∷ xs ≡ y ∷ ys → x ≡ y
∷-injectiveˡ refl = refl

∷-injectiveʳ : ∀{i}{A : Set i}{n : ℕ}{x y : A}{xs ys : Vec A n} →
  x ∷ xs ≡ y ∷ ys → xs ≡ ys
∷-injectiveʳ refl = refl

∷-injective : ∀{i}{A : Set i}{n : ℕ}{x y : A}{xs ys : Vec A n} → 
  (x ∷ xs) ≡ (y ∷ ys) → x ≡ y × xs ≡ ys
∷-injective refl = refl , refl

∷-dec : ∀{i}{A : Set i}{n : ℕ}{x y : A}{xs ys : Vec A n} → Dec (x ≡ y) → Dec (xs ≡ ys) → Dec (x ∷ xs ≡ y ∷ ys)
∷-dec (no p) _ = no λ e → p (∷-injectiveˡ e)
∷-dec (yes p) (no q) = no λ e → q (∷-injectiveʳ e)
∷-dec (yes refl) (yes refl) = yes refl

≡-dec-Vec : ∀{i}{A : Set i}{n : ℕ} → DecidableEquality A → DecidableEquality (Vec A n)
≡-dec-Vec _≟_ []       []       = yes refl
≡-dec-Vec _≟_ (x ∷ xs) (y ∷ ys) = ∷-dec (x ≟ y) (≡-dec-Vec _≟_ xs ys)