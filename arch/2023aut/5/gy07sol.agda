open import Lib

---------------------------------------------------------
-- propositional logic
------------------------------------------------------

subt-prod : {A A' B B' : Set} → (A → A') → (B → B') → A × B → A' × B'
subt-prod f g (a , b) = f a , g b

subt-fun : {A A' B B' : Set} → (A → A') → (B → B') → (A' → B) → (A → B')
subt-fun f g h a = g (h (f a))

-- C-u C-u C-c C-'
anything : {X Y : Set} → ¬ X → X → Y
anything nx x = exfalso (nx x)

ret : {X : Set} → X → ¬ ¬ X
ret = {!!}

fun : {X Y : Set} → (¬ X) ⊎ Y → (X → Y)
fun = {!!}

-- De Morgan

dm1 : {X Y : Set} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
dm1 = {!!}

-- ez miért csak abba az irányba?
dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 (inl nx) (x , y) = nx x
dm2 (inr ny) (x , y) = ny y

-- ezt miért ilyen furán írjuk fel?
dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b f = f λ n[xay] -> inl λ x -> f λ _ -> inr λ y -> n[xay] (x , y)

-- miért nem lehet ezt definiálni?
¬¬ : {X : Set} → ¬ ¬ X → X
¬¬ nnx = exfalso (nnx λ x -> nnx λ x -> nnx λ x -> {!!})

----------------------------------
-- a szent lem
-- lem : {X : Set} → (X ⊎ ¬ X)
----------------------------------

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

-- you have to decide:
{-
Dec : Set → Set
Dec A = A ⊎ ¬ A
-}

open import Lib.Dec.PatternSynonym

ee1 : {X Y : Set} → Dec (X ⊎ Y → ¬ ¬ (Y ⊎ X))
ee1 = inl λ xvy -> λ f -> f (case xvy (λ x -> inr x) λ y -> inl y)           -- C-u C-u C-c C-,

ee2 : {X : Set} → Dec (¬ (X ⊎ ¬ X))
ee2 = inr λ f -> f (inr λ x -> f (inl x))

e3 : {X : Set} → Dec (¬ (X → (¬ X → X)))
e3 = inr λ f -> f λ x nx -> exfalso (nx x)

e4 : Dec ℕ
e4 = inl 42

e5 : Dec ⊥
e5 = inr λ b -> b

e6 : {X : Set} → Dec (⊥ → X ⊎ ¬ X)
e6 = inl λ b -> exfalso b

e7 : {X : Set} → Dec (X × ¬ X → ¬ X ⊎ X)
e7 = inl λ {(x , nx) -> inr x}

e8 : {X : Set} → Dec ((X → X) → ⊥)
e8 = inr λ f -> f λ x -> x

f1 : {X Y : Set} → ¬ ¬ X ⊎ ¬ ¬ Y → ¬ ¬ (X ⊎ Y)
f1 = λ nnxvnny n[xvy] -> case nnxvnny (λ nnx -> nnx λ x -> n[xvy] (inl x))
                                       λ nny -> nny λ y -> n[xvy] (inr y)

f2 : ({X Y : Set} → ¬ (X × Y) → ¬ X ⊎ ¬ Y) → {X Y : Set} → ¬ ¬ (X ⊎ Y) → ¬ ¬ X ⊎ ¬ ¬ Y
f2 = λ f {X} {Y} nn[xvy] -> f {¬ X} {¬ Y} λ {(nx , ny) -> nn[xvy] λ xvy ->
                                                                   case xvy nx ny}
