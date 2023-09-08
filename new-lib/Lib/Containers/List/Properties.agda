{-# OPTIONS --safe #-}

module Lib.Containers.List.Properties where

open import Lib.Containers.List.Type
open import Lib.Containers.List.Base
open import Lib.Equality
open import Lib.Dec
open import Lib.Sigma
open import Lib.Empty
open import Lib.Unit

∷-injective : ∀{i}{A : Set i}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
∷-injective refl = (refl , refl)

∷-injectiveˡ : ∀{i}{A : Set i}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
∷-injectiveˡ refl = refl

∷-injectiveʳ : ∀{i}{A : Set i}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
∷-injectiveʳ refl = refl

∷-dec : ∀{i}{A : Set i}{x y : A}{xs ys : List A} → Dec (x ≡ y) → Dec (xs ≡ ys) → Dec (x ∷ xs ≡ y ∷ ys)
∷-dec (no p) xs=ys = no λ e → p (∷-injectiveˡ e)
∷-dec (yes p) (no q) = no λ e → q (∷-injectiveʳ e)
∷-dec (yes refl) (yes refl) = yes refl

≡-dec-List : ∀{i}{A : Set i} → DecidableEquality A → DecidableEquality (List A)
≡-dec-List _≟_ []       []       = yes refl
≡-dec-List _≟_ (x ∷ xs) []       = no λ()
≡-dec-List _≟_ []       (y ∷ ys) = no λ()
≡-dec-List _≟_ (x ∷ xs) (y ∷ ys) = ∷-dec (x ≟ y) (≡-dec-List _≟_ xs ys)