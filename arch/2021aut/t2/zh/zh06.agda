module zh06 where
open import lib
--      x                       y
task1 : (((ℕ → ⊥) → ⊥) ⊎ ⊥) → (ℕ → (((ℕ → ⊥) → ⊥) ⊎ ⊥) → (𝟚 ⊎ ℕ → ⊥)) ⊎ ⊥ → (𝟚 → ⊥)
task1 = λ x y → case x ( λ t₁ →  case y (λ t → {-nehez-} λ b → t 10 (ι₁ t₁) (ι₂ 10))  λ t → {-konnyu-} λ b → t)  λ t → {-konnyu-} λ b → t
