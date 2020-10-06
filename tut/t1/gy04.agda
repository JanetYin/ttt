module tut.t1.gy04 where

open import lib

idr : {A : Set} → A ⊎ ⊥ ↔ A     -- (A ∨ ⊥ → A) ∧ (A → A ∨ ⊥)
idr = (λ u → case u (λ x → x) exfalso) , λ a → inj₁ a

-- logic

anything : {X Y : Set} →  ¬ X → X → Y
anything = {!!}

ret : {X : Set} → X → ¬ ¬ X
ret = {!!}

fun : {X Y : Set} → (¬ X) ⊎ Y → (X → Y)
fun = {!!}

-- De Morgan

dm1 : {X Y : Set} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
dm1 = {!!}

dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 = {!!}

dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b = {!!}

-- stuff

nocontra : {X : Set} → ¬ (X ↔ ¬ X)
nocontra = {!!}

¬¬invol₁ : {X : Set} → ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
¬¬invol₁ = {!!}

¬¬invol₂ : {X : Set} → ¬ ¬ ¬ X ↔ ¬ X
¬¬invol₂ = {!!}

nnlem : {X : Set} → ¬ ¬ (X ⊎ ¬ X)
nnlem = {!!}

nndnp : {X : Set} → ¬ ¬ (¬ ¬ X → X)
nndnp = {!!}

dec2stab : {X : Set} → (X ⊎ ¬ X) → (¬ ¬ X → X)
dec2stab = {!!}

-- the other direction does not hold, but (this is a bit tricky to read):

dnp2lem : ({X : Set} → (¬ ¬ X → X)) → ({X : Set} → (X ⊎ ¬ X))
dnp2lem dnp {X} = {!!}

a4 : {A B : Set} → ⊥ ⊎ ((A → B) × A) ↔ A × B
a4 = {!!}
