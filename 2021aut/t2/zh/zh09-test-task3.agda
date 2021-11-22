module zh09-test-task3 where
open import lib
open import Agda.Primitive
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

id : 𝟚 → 𝟚
id x = x

test-task3-id-tt : {eq₁ : Eq𝟚 (id tt) tt}{eq₂ : Eq𝟚 (id tt) (id tt)} → Eq (Eq𝟚 (id tt) tt ⊎ Eq𝟚 (id tt) ff) (task {id} {tt} eq₁ eq₂) (ι₁ triv)
test-task3-id-tt = refl
test-task3-id-ff : {eq₁ : Eq𝟚 (id ff) ff}{eq₂ : Eq𝟚 (id ff) (id ff)} → Eq (Eq𝟚 (id ff) tt ⊎ Eq𝟚 (id ff) ff) (task {id} {ff} eq₁ eq₂) (ι₂ triv)
test-task3-id-ff = refl

not : 𝟚 → 𝟚
not x = if x then ff else tt

test-task3-not-tt : {eq₁ : Eq𝟚 (not tt) tt}{eq₂ : Eq𝟚 (not tt) (not tt)} → Eq (Eq𝟚 (not tt) tt ⊎ Eq𝟚 (not tt) ff) (task {not} {tt} eq₁ eq₂) (ι₂ triv)
test-task3-not-tt = refl
test-task3-not-ff : {eq₁ : Eq𝟚 (not ff) ff}{eq₂ : Eq𝟚 (not ff) (not ff)} → Eq (Eq𝟚 (not ff) tt ⊎ Eq𝟚 (not ff) ff) (task {not} {ff} eq₁ eq₂) (ι₁ triv)
test-task3-not-ff = refl

ct : 𝟚 → 𝟚
ct _ = tt

test-task3-ct-tt : {eq₁ : Eq𝟚 (ct tt) tt}{eq₂ : Eq𝟚 (ct tt) (ct tt)} → Eq (Eq𝟚 (ct tt) tt ⊎ Eq𝟚 (ct tt) ff) (task {ct} {tt} eq₁ eq₂) (ι₁ triv)
test-task3-ct-tt = refl
test-task3-ct-ff : {eq₁ : Eq𝟚 (ct ff) ff}{eq₂ : Eq𝟚 (ct ff) (ct ff)} → Eq (Eq𝟚 (ct ff) tt ⊎ Eq𝟚 (ct ff) ff) (task {ct} {ff} eq₁ eq₂) (ι₁ triv)
test-task3-ct-ff = refl

cf : 𝟚 → 𝟚
cf _ = ff

test-task3-cf-tt : {eq₁ : Eq𝟚 (cf tt) tt}{eq₂ : Eq𝟚 (cf tt) (cf tt)} → Eq (Eq𝟚 (cf tt) tt ⊎ Eq𝟚 (cf tt) ff) (task {cf} {tt} eq₁ eq₂) (ι₂ triv)
test-task3-cf-tt = refl
test-task3-cf-ff : {eq₁ : Eq𝟚 (cf ff) ff}{eq₂ : Eq𝟚 (cf ff) (cf ff)} → Eq (Eq𝟚 (cf ff) tt ⊎ Eq𝟚 (cf ff) ff) (task {cf} {ff} eq₁ eq₂) (ι₂ triv)
test-task3-cf-ff = refl
