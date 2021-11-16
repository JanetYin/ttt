module test-zh08 where
import zh08
open import lib

test-task1-1 : {A B : Set}{a : A}{b : B}{bot : ⊥} →
  Eq ⊥ bot (zh08.task1 {A} {B} λ t → t ((λ a → bot) , (λ b → bot)) (ι₁ a))
test-task1-1 = refl

test-task1-2 : {A B : Set}{a : A}{b : B}{bot : ⊥} →
  Eq ⊥ bot (zh08.task1 {A} {B} λ t → t ((λ a → bot) , (λ b → bot)) (ι₂ b))
test-task1-2 = refl

-- only checking the type:
test-task2 : {A B : Set} → ¬ (¬ A × ¬ B → ¬ (A ⊎ B)) → A × B
test-task2 = zh08.task2
-- manual check later
