module zh09-test-task1 where
open import lib
import zh09

task = zh09.task
Eq𝟚 = zh09.Eq𝟚

test-Eq𝟚 :  Eq Set (
  ( Eq𝟚 tt tt
  × Eq𝟚 ff ff
  × Eq𝟚 tt ff
  × Eq𝟚 ff tt
  )) (⊤ × ⊤ × ⊥ × ⊥)
test-Eq𝟚 = refl

--test-task1-x : {f : 𝟚 → 𝟚} → {eq₁ : Eq𝟚 (f x) x}{eq₂ : Eq𝟚 (f x) (f x)} → Eq (Eq𝟚 (f x) tt ⊎ Eq𝟚 (f x) ff) (task {f} {x} eq₁ eq₂) (ι₁ eq₁)
test-task1-tt : {f : 𝟚 → 𝟚} → {eq₁ : Eq𝟚 (f tt) tt}{eq₂ : Eq𝟚 (f tt) (f tt)} → Eq (Eq𝟚 (f tt) tt ⊎ Eq𝟚 (f tt) ff) (task {f} {tt} eq₁ eq₂) (ι₁ eq₁)
test-task1-ff : {f : 𝟚 → 𝟚} → {eq₁ : Eq𝟚 (f ff) ff}{eq₂ : Eq𝟚 (f ff) (f ff)} → Eq (Eq𝟚 (f ff) tt ⊎ Eq𝟚 (f ff) ff) (task {f} {ff} eq₁ eq₂) (ι₂ eq₁)
test-task1-tt = refl
test-task1-ff = refl
