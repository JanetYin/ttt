open import Agda.Builtin.Sigma
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

data ⊥ : Set where

¬_ : ∀ {i} → Set i → Set i
¬ A = A → ⊥

-- ha minden ajtóhoz létezik kulcs, ami nyitja; attól még nem feltétlen létezik olyan kulcs, ami minden ajtót nyit
Σ∀'       : ¬ ((A B : Set)(R : A → B → Set) →
               (∀ (b : B) → Σ A λ a → R a b) → (Σ A λ a → ∀ (b : B) → R a b))
-- segítség: A = Bool, B = Bool, R = _≡_ jó példa
-- meg raktam be ilyen helpert, de a false ≡ true-ra meg a true ≡ false-ra kellhet még
Σ∀' f = helper (f Bool Bool _≡_ {!!})
  where
  helper : Σ Bool (λ a → (b : Bool) → a ≡ b) → ⊥
  helper (false , hyp) = {!!}
  helper (true , hyp) = {!!}
