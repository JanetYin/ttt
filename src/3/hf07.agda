module hf07 where

open import Lib

{-
contradiction : ∀{i j}{P : Set i}{Whatever : Set j} → P → ¬ P → Whatever
contradiction p ¬p = exfalso (¬p p)

contraposition : ∀{i j}{P : Set i}{Q : Set j} → (P → Q) → ¬ Q → ¬ P
contraposition f ¬q p = contradiction (f p) ¬q

weaken : {X : Set} → X → ¬ ¬ X
weaken x = λ ¬x → ¬x x
-}

dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 = {!   !}

dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b = {!   !}

-- stuff

nocontra : {X : Set} → ¬ (X ↔ ¬ X)
nocontra = {!   !}

¬¬invol₁ : {X : Set} → ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
¬¬invol₁ = {!   !}

¬¬invol₂ : {X : Set} → ¬ ¬ ¬ X ↔ ¬ X
¬¬invol₂ = {!   !}

nndnp : {X : Set} → ¬ ¬ (¬ ¬ X → X)
nndnp = {!   !}

dec2stab : {X : Set} → (X ⊎ ¬ X) → (¬ ¬ X → X)
dec2stab = {!   !}

open import Lib.Dec.PatternSynonym

e3 : {X : Set} → Dec (¬ (X → (¬ X → X)))
e3 = {!   !}

e4 : Dec ℕ
e4 = {!   !}

e5 : Dec ⊥
e5 = {!   !}

e6 : {X : Set} → Dec (⊥ → X ⊎ ¬ X)
e6 = {!   !}

e7 : {X : Set} → Dec (X × ¬ X → ¬ X ⊎ X)
e7 = {!   !}

e8 : {X : Set} → Dec ((X → X) → ⊥)
e8 = {!   !}

e9 : {X Y : Set} → Dec (X ⊎ Y ↔ (¬ X → Y))
e9 = {!   !}

e10 : {X Y : Set} → Dec ((¬ X → ¬ Y) → Y → X)
e10 = {!   !}

f1 : {X Y : Set} → ¬ ¬ X ⊎ ¬ ¬ Y → ¬ ¬ (X ⊎ Y)
f1 = {!   !}

f2 : ({X Y : Set} → ¬ (X × Y) → ¬ X ⊎ ¬ Y) → {X Y : Set} → ¬ ¬ (X ⊎ Y) → ¬ ¬ X ⊎ ¬ ¬ Y
f2 = {!   !}