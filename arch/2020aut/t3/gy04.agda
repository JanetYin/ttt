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
dm1 = (λ nxy → (λ x → nxy (inj₁ x)) , λ y → nxy (inj₂ y))
    , λ p → λ xy → case xy (proj₁ p) (proj₂ p)

-- ¬ X V ¬ Y ⇒ ¬ (X ∧ Y)
dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 = λ nxny → λ xy → case nxny (λ nx → nx (proj₁ xy)) λ ny → ny (proj₂ xy)

--nincs: ¬ (X ∧ Y) ⇒ ¬ X V ¬ Y 
dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b = λ w → w λ nxy → inj₁ λ x → w λ nxy2 → inj₂ λ y → nxy (x , y)

-- stuff

nocontra : {X : Set} → ¬ (X ↔ ¬ X)
nocontra = λ contra → let x = (proj₂ contra (λ x → proj₁ contra x x)) in proj₁ contra x x

¬¬invol₁ : {X : Set} → ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
¬¬invol₁ = (λ nnnnx nx → nnnnx λ nnnx → nnnx nx)
         , λ nnx nnnx → nnnx nnx

¬¬invol₂ : {X : Set} → ¬ ¬ ¬ X ↔ ¬ X
¬¬invol₂ = (λ nnnx x → nnnx λ nx → nx x)
         , λ nx nnx → nnx nx

nnlem : {X : Set} → ¬ ¬ (X ⊎ ¬ X)
nnlem = λ nkk → nkk (inj₂ λ x → nkk (inj₁ x))

nndnp : {X : Set} → ¬ ¬ (¬ ¬ X → X)
nndnp = λ dnp → dnp λ nnx → exfalso (nnx λ x → dnp λ nnx2 → x)

dec2stab : {X : Set} → (X ⊎ ¬ X) → (¬ ¬ X → X)
dec2stab = λ kk nnx → case kk (λ x → x) λ nx → exfalso (nnx nx)

-- the other direction does not hold, but (this is a bit tricky to read):

dnp2lem : ({X : Set} → (¬ ¬ X → X)) → ({X : Set} → (X ⊎ ¬ X))
dnp2lem dnp {X} = dnp {X ⊎ ¬ X} nnlem
