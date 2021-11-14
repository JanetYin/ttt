{-# OPTIONS --allow-unsolved-metas #-}
module zh07-test where
open import lib
import zh07

test-type : {X : Set} → ¬ ¬ ¬ X ↔ ¬ X
test-type = zh07.task1

test-left : Eq ({X : Set} → ¬ ¬ ¬ X → ¬ X) (π₁ zh07.task1) λ z z₁ → z (λ z₂ → z₂ z₁)
test-left = refl

test-right : Eq ({X : Set} → ¬ X → ¬ ¬ ¬ X) (π₂ zh07.task1) λ z z₁ → z₁ z
test-right = refl

test-full : Eq ({X : Set} → ¬ ¬ ¬ X ↔ ¬ X) zh07.task1 ((λ x x₁ → x (λ x₂ → x₂ x₁)) , (λ x x₁ → x₁ x))
test-full = refl
