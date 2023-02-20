module zh05-test where
open import lib
import zh05

test-task1 : Eq (((⊤ × ⊥) ⊎ ⊤) × (⊤ ⊎ ⊥)) (ι₂ triv , ι₁ triv) zh05.task1
test-task1 = refl

test-task2 : Eq (⊥ → ⊤ × ⊥) (λ bot → triv , bot) (λ bot → zh05.task2 bot)
test-task2 = refl

test-task3-1 : Eq (⊥ → ⊤ × ⊥) (λ bot → triv , bot) (λ bot → zh05.task3 (ι₁ (bot , triv)))
test-task3-1 = refl
test-task3-2 : Eq (⊥ → ⊤ × ⊥) (λ bot → triv , bot) (λ bot → zh05.task3 (ι₂ (bot , triv)))
test-task3-2 = refl
