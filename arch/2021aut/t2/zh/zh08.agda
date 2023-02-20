{-# OPTIONS --allow-unsolved-metas #-}
module zh08 where
open import lib

task1 : {A B : Set} → ¬ (¬ A × ¬ B → ¬ (A ⊎ B)) → ⊥
task1 {A} {B} nlem = nlem λ { (na , nb) → λ ab → case ab (λ a → na a) λ b → nb b }
task2 : {A B : Set} → ¬ (¬ A × ¬ B → ¬ (A ⊎ B)) → A × B
task2 {A} {B} nlem = exfalso (task1 nlem)
