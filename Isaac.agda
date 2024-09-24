{-# OPTIONS --cubical --safe #-}
-- open import Cubical.Core.Prelude
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Fin
open import Data.Maybe.Base
open import Cubical.Data.Nat

module Isaac where
isaac : ∀ {n} → Maybe (Fin n) ≡ Fin (suc n)
isaac {n} = isoToPath (iso f g p q)
  where
  f1: ℕ → ℕ 
  f1 = ?
  f : Maybe (Fin n) → Fin (suc n)
  f (just x) = fsuc x
  f nothing = fzero
  g : Fin (suc n) → Maybe (Fin n)
  g (zero , snd₁) = nothing
  g (suc a , fst₁ , snd₁) = just ((a , fst₁ , λ i → {! (λ (suc x) → x) (snd₁ i) !}))
  p : section f g
  p a = {!   !}
  q : retract f g
  q a = {!   !}
