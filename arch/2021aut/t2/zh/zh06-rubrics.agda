module zh06-rubrics where
open import lib

test1 : Set
test1 = ? ⊎ ⊥ → ? ⊎ ⊥ → 𝟚 → ⊥

test2 : Set
test2 = ((ℕ → ⊥) → ⊥) ⊎ ? → (((ℕ → ⊥) → ⊥) ⊎ ⊥) → (𝟚 ⊎ ℕ → ⊥)) ⊎ ? → 𝟚 → ⊥
