{-# OPTIONS --safe --guardedness #-}
module Lib.CoFin.Base where

open import Lib.CoFin.Type
open import Lib.Conat.Type
open import Lib.Conat.Base
open import Lib.Conat.Literals
open import Lib.Maybe.Type
open import Lib.Sigma.Type
open import Lib.Function
open import Lib.Sum.Type
open import Lib.Empty.Type
open import Lib.Empty.Base
open import Lib.Unit.Type
open import Lib.Equality.Type
open import Lib.Equality.Base
open import Lib.Containers.CoVector.Type
-- open import Lib.WorkInProgressConcept.DoNotIncludeInLib.Lazy

f∞ : CoFin ∞
fpred∞ f∞ = just f∞

coiteCoFin : ∀{ℓ}{n : ℕ∞}(P : ℕ∞ → Set ℓ) →
  (ginz : ({n : ℕ∞} → P n → IsNotZero∞ n)) →
  (gfpred∞ : {n : ℕ∞} → (p : P n) → Maybe (P (predℕ∞ n ⦃ ginz p ⦄))) →
  (seed : P n) →
  CoFin n
inz (coiteCoFin P ginz gfpred∞ seed) = ginz seed
fpred∞ (coiteCoFin P ginz gfpred∞ seed) with gfpred∞ seed
... | just x = just (coiteCoFin P ginz gfpred∞ x)
... | nothing = nothing

opaque -- sztem segít
  coiteCoFinΣ : ∀{ℓ}{n : ℕ∞}(P : ℕ∞ → Set ℓ) →
    (gen : {n : ℕ∞} → P n → Σ (IsNotZero∞ n) λ p → Maybe (P (predℕ∞ n ⦃ p ⦄))) →
    (seed : P n) →
    CoFin n
  coiteCoFinΣ P gen seed = coiteCoFin P (fst ⊚ gen) (snd ⊚ gen) seed

  coiteCoFinιΣ : ∀{ℓ}{n : ℕ∞}(P : ℕ∞ → Set ℓ) →
    (gen : {n : ℕ∞} → P n → ιΣ (IsNotZero∞ n) (Maybe (P (predℕ∞ n)))) →
    (seed : P n) →
    CoFin n
  coiteCoFinιΣ P gen seed = coiteCoFinΣ P gen seed -- coiteCoFinΣ P (fst ιΣ↔Σ ⊚ gen) seed

singular-cof1 : (c : CoFin 1) → fpred∞ c ≡ nothing
singular-cof1 c with fpred∞ c
... | just x = exfalso (coz x)
... | nothing = refl

cof1 : CoFin 1
fpred∞ cof1 = nothing

cof2-1 : CoFin 2
fpred∞ cof2-1 = nothing

cof2-2 : CoFin 2
fpred∞ cof2-2 = just cof1

diff : cof2-1 ≢ cof2-2
diff x with cong fpred∞ x
... | ()
{-
uniq : (a : CoFin 2) → fpred∞ a ≡ fpred∞ cof2-1 ⊎ fpred∞ a ≡ fpred∞ cof2-2
uniq a with fpred∞ a
... | just x = inr (cong just {!!})
... | nothing = inl refl

_‼ᶜ_ : ∀{ℓ}{A : Set ℓ}{n : ℕ∞} → CoVec A n → CoFin n → Lazy A
cs ‼ᶜ f with fpred∞ f
... | just x = later (delay {!!}) -- TODO Marci, hajrá! :D
... | nothing = now (head cs ⦃ inz f ⦄)
-}
