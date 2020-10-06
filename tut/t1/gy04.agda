module tut.gy04 where

open import lib

-- logic

anything : {X Y : Set} →  ¬ X → X → Y
anything = λ nx x → exfalso (nx x)

ret : {X : Set} → X → ¬ ¬ X
ret = λ x → λ nx → nx x

fun : {X Y : Set} → (¬ X) ⊎ Y → (X → Y)
fun = λ w x → case w (λ nx → exfalso (nx x)) (λ y → y)

-- De Morgan

dm1 : {X Y : Set} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
dm1 = (λ w → (λ x → w (inj₁ x)) , (λ y → w (inj₂ y) )) , λ w xy → case xy (λ x → proj₁ w x) λ y → proj₂ w y

dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 = λ w xy → case w (λ nx → nx (proj₁ xy)) λ ny → ny (proj₂ xy)

dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b = λ w → w λ nxy → inj₁ λ x → w λ nxy' → inj₂ λ y → nxy (x , y)

-- stuff

nocontra : {X : Set} → ¬ (X ↔ ¬ X)
nocontra = λ w → let x = (proj₂ w (λ x → proj₁ w x x)) in proj₁ w x x

¬¬invol₁ : {X : Set} → ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
¬¬invol₁ = (λ w nx → w λ nnx → nnx nx) , λ nnx nnnx → nnnx nnx

¬¬invol₂ : {X : Set} → ¬ ¬ ¬ X ↔ ¬ X
¬¬invol₂ = (λ nnnx x → nnnx λ nx → nx x) , λ nx nnx → nnx nx

nnlem : {X : Set} → ¬ ¬ (X ⊎ ¬ X)
nnlem = λ nlem → nlem (inj₂ λ x → nlem (inj₁ x))

nndnp : {X : Set} → ¬ ¬ (¬ ¬ X → X)
nndnp = λ w → w λ nnx → exfalso (nnx λ x → w λ _ → x)

dec2stab : {X : Set} → (X ⊎ ¬ X) → (¬ ¬ X → X)
dec2stab = λ lem nnx → case lem (λ x → x) λ nx → exfalso (nnx nx)

-- the other direction does not hold, but (this is a bit tricky to read):

dnp2lem : ({X : Set} → (¬ ¬ X → X)) → ({X : Set} → (X ⊎ ¬ X))
dnp2lem dnp {X} = dnp {X ⊎ ¬ X} nnlem
