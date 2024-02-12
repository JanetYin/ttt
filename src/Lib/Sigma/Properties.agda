{-# OPTIONS --safe #-}

module Lib.Sigma.Properties where

open import Lib.Sigma.Type
open import Lib.Sigma.Base
open import Lib.Equality
open import Lib.Dec
open import Lib.Dec.PatternSynonym
open import Lib.Unit
open import Lib.Empty
open import Lib.Bool.Type

Σinj : ∀{i j}{A : Set i}{B : A → Set j}{a b : Σ A B} →
  (eq : a ≡ b) → (fst a ≡ fst b) × (subst B (cong fst eq) (snd a) ≡ snd b)
Σinj refl = refl , refl

infixr 4 _,=_
_,=_ : ∀{i j}{A : Set i}{B : A → Set j}{a b : A}{x : B a}{y : B b} →
  (eq : a ≡ b) → (eq2 : subst B eq x ≡ y) → _≡_ {A = Σ A B} (a , x) (b , y)
refl ,= refl = refl

×inj : ∀{i j}{A : Set i}{B : Set j}{a b : A × B} →
  (a ≡ b) ↔ (fst a ≡ fst b) × (snd a ≡ snd b)
×inj = (λ {refl → refl , refl}) , (λ {(refl , refl) → refl})

,-dec : ∀{i j}{A : Set i}{B : Set j}{a c : A}{b d : B} →
  Dec (a ≡ c) → Dec (b ≡ d) → Dec ((a , b) ≡ (c , d))
,-dec (no p) _ = no λ {refl → p refl}
,-dec (yes p) (no q) = no λ {refl → q refl}
,-dec (yes refl) (yes refl) = yes refl

×-dec : ∀{i j}{A : Set i}{B : Set j} → Dec A → Dec B → Dec (A × B)
×-dec (no p)  _       = no λ ab → p (fst ab)
×-dec (yes p) (no q)  = no λ ab → q (snd ab)
×-dec (yes p) (yes q) = yes (p , q)

Σ-dec : ∀{i j}{A : Set i}{B : A → Set j}
    → ((a b : A) → Dec (a ≡ b))
    → (∀{a} → ((b c : B a) → Dec (b ≡ c)))
    → (x y : Σ A B) → Dec (x ≡ y)
Σ-dec e1 e2 (x1 , x2) (y1 , y2) with e1 x1 y1
... | no b  = no λ {refl → b refl}
... | yes refl with e2 x2 y2
... | yes a = yes (refl ,= a)
... | no b = no λ {refl → b refl}