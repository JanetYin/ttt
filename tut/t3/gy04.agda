module tut.t3.gy04 where

open import lib

-- ¬ A = A → ⊥ 
-- ¬ ≡ \neg

--nincs: ¬ ¬ A → A
--nincs: A ⊎ ¬ A
--Az A klasszikus logikában igaz akkor és csak akkor ha ¬ ¬ A konstruktív logikában igaz

anything : {X Y : Set} → ¬ X → X → Y
anything = λ nx → λ x → exfalso (nx x)

ret : {X : Set} → X → ¬ ¬ X
ret = λ x → λ nx → nx x

fun : {X Y : Set} → (¬ X) ⊎ Y → (X → Y)
fun = λ nxy → λ x → case nxy (λ nx → exfalso (nx x)) λ y → y

-- De Morgan

dm1 : {X Y : Set} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
dm1 = {!!}

-- ¬ X V ¬ Y ⇒ ¬ (X ∧ Y)
dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 = {!!}

--nincs: ¬ (X ∧ Y) ⇒ ¬ X V ¬ Y 
dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b = λ w → w λ nxy → inj₁ λ x → w λ nxy2 → inj₂ λ y → nxy (x , y)

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
