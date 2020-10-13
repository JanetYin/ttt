module tut.t1.gy04 where

open import lib

-- negáció
-- ¬ A = A → ⊥
-- ¬ = \neg

-- a logikánk nem a klasszikus logika
-- nincs lem: A ⊎ ¬ A
-- dne sincs: ¬ ¬ A → A 
-- intuicionista logikánk van
-- A klasszikus logikában A bizonyítható ↔ ¬ ¬ A intuicionista logikában bizonyítható

idr : {A : Set} → A ⊎ ⊥ ↔ A     -- (A ∨ ⊥ → A) ∧ (A → A ∨ ⊥)
idr = (λ u → case u (λ x → x) exfalso) , λ a → inj₁ a

-- C-u, C-u, C-c, C-, -- goal and context fully normalised
-- C-u, C-u, C-c, C-. -- goal context and inferred type of given expression fully normalised
-- logic

anything : {X Y : Set} → ¬ X → X → Y
anything = λ nx → λ x → exfalso (nx x)

-- ¬ (¬ X) = ¬ X → ⊥ = (X → ⊥) → ⊥ 
ret : {X : Set} → X → ¬ ¬ X
ret = λ x nx → nx x

fun : {X Y : Set} → (¬ X) ⊎ Y → (X → Y)
fun = λ nx∨y x → case nx∨y (λ nx → anything nx x) λ y → y

-- De Morgan

dm1 : {X Y : Set} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
dm1 = (λ u → (λ x → u (inj₁ x)) , λ y → u (inj₂ y))
    , λ u v → case v (proj₁ u) (proj₂ u)

dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 = λ u v → case u (λ nx → nx (proj₁ v)) λ ny → ny (proj₂ v)

dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y) -- = ¬ (¬ F) = ¬ (F → ⊥) = (F → ⊥) → ⊥
dm2b = λ u → u λ v → inj₁ λ x → u λ t → inj₂ λ y → v (x , y)

-- stuff

nocontra : {X : Set} → ¬ (X ↔ ¬ X)
nocontra = λ u → proj₁ u (proj₂ u (λ x → proj₁ u x x)) ((proj₂ u (λ x → proj₁ u x x)))

¬¬invol₁ : {X : Set} → ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
¬¬invol₁ = (λ u v → u λ t → t v)
         , λ u v → v u

¬¬invol₂ : {X : Set} → ¬ ¬ ¬ X ↔ ¬ X
¬¬invol₂ = {!!}

nnlem : {X : Set} → ¬ ¬ (X ⊎ ¬ X)
nnlem = λ u → u (inj₂ λ x → u (inj₁ x))

nndnp : {X : Set} → ¬ ¬ (¬ ¬ X → X)
nndnp = λ u → u λ v → exfalso (v λ x → u λ t → x)

dec2stab : {X : Set} → (X ⊎ ¬ X) → (¬ ¬ X → X)
dec2stab = λ u v → case u (λ x → x) λ nx → exfalso (v nx)

-- the other direction does not hold, but (this is a bit tricky to read):

dnp2lem : ({X : Set} → (¬ ¬ X → X)) → ({X : Set} → (X ⊎ ¬ X))
dnp2lem dnp {X} = dnp nnlem
