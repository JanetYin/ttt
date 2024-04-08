{-# OPTIONS --safe --guardedness #-}

module Lib.Containers.CoList.Properties where

open import Lib.Containers.CoList.Type
open import Lib.Containers.CoList.Base
open import Lib.Containers.CoList.Bisimilarity
open import Lib.Containers.CoList.PatternSynonym
open import Lib.Maybe.Type
open import Lib.Equality.Type
open import Lib.Equality.Base
open import Lib.Sigma.Type
open import Lib.Conat.Type
open import Lib.Conat.PatternSynonym
open import Lib.Conat.Equality

reflL : ∀{i}{A : Set i}(xs : CoList A) → xs ≈L xs
reflL′ : ∀{i}{A : Set i}(xs : Maybe (A × CoList A)) → xs ≈L′ xs
reflL′ []∞ = _
reflL′ (x ∷∞ xs) = refl , reflL xs
prove (reflL xs) = reflL′ (uncons xs)

symL : ∀{i}{A : Set i}{xs ys : CoList A} → xs ≈L ys → ys ≈L xs
symL′ : ∀{i}{A : Set i}{xs ys : Maybe (A × CoList A)} → xs ≈L′ ys → ys ≈L′ xs
symL′ {xs = []∞} {[]∞} e = e
symL′ {xs = x ∷∞ xs} {y ∷∞ ys} (xy , xsys) = (sym xy) , (symL xsys)
prove (symL e) = symL′ (prove e)

transL : ∀{i}{A : Set i}{xs ys zs : CoList A} → xs ≈L ys → ys ≈L zs → xs ≈L zs
transL′ : ∀{i}{A : Set i}{xs ys zs : Maybe (A × CoList A)} → xs ≈L′ ys → ys ≈L′ zs → xs ≈L′ zs
transL′ {xs = []∞} {[]∞} {zs} e1 e2 = e2
transL′ {xs = x ∷∞ xs} {.x ∷∞ ys} {z ∷∞ zs} (refl , e1) (refl , e2) = refl , transL e1 e2
prove (transL e1 e2) = transL′ (prove e1) (prove e2)

CoList-η : ∀{i}{A : Set i}(xs : CoList A) → mkCoList (uncons xs) ≈L xs
prove (CoList-η xs) = reflL′ (uncons xs)

length-coreplicate : ∀{i}{A : Set i}(n : ℕ∞)(xs : CoList A) → 
  length (coreplicate n xs) ≈ℕ∞ n
prove (length-coreplicate n xs) with pred∞ n
... | zero∞  = _
... | suc∞ b = length-coreplicate b xs

length-repeat-∞ : ∀{i}{A : Set i}(xs : CoList A) → length (repeat xs) ≈ℕ∞ ∞
length-repeat-∞ = length-coreplicate ∞
