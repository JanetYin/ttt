module gy07 where

open import lib

---------------------------------------------------------
-- propositional logic
------------------------------------------------------

-- C1 : A ⊃ B ⊃ A ∧ B

subt-prod : {A A' B B' : Set} → (A → A') → (B → B') → A × B → A' × B'
subt-prod f g (a , b) = f a , g b

subt-fun : {A A' B B' : Set} → (A → A') → (B → B') → (A' → B) → (A → B')
subt-fun f g h a = g (h (f a))

contradiction : {X Y : Set} → ¬ X → X → Y
contradiction ¬x x = exfalso (¬x x)

weaken : {X : Set} → X → ¬ ¬ X
weaken x = λ ¬x → ¬x x

{-
hard : {X : Set} → ¬ ¬ X → X
hard ¬¬x = exfalso (¬¬x λ x → ¬¬x λ x₁ → {!   !})
-}

fun : {X Y : Set} → (¬ X) ⊎ Y → (X → Y)
fun (inl ¬x) x = contradiction ¬x x
fun (inr y) x = y

-- De Morgan

dm1 : {X Y : Set} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
dm1 = to , from where
  to : {X Y : Set} → ¬ (X ⊎ Y) → ¬ X × ¬ Y
  to f = (λ x → f (inl x)) , λ y → f (inr y)

  from : {X Y : Set} → ¬ X × ¬ Y → ¬ (X ⊎ Y)
  from (¬x , ¬y) (inl x) = ¬x x
  from (¬x , ¬y) (inr y) = ¬y y
  
dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 (inl ¬x) (x , y) = ¬x x
dm2 (inr ¬y) (x , y) = ¬y y

dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b f = f (λ ¬xy → inl (λ x → f λ ¬xy2 → inr λ y → ¬xy (x , y)))

-- stuff

nocontra : {X : Set} → ¬ (X ↔ ¬ X)
nocontra = {!!}

¬¬invol₁ : {X : Set} → ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
¬¬invol₁ = {!!}

¬¬invol₂ : {X : Set} → ¬ ¬ ¬ X ↔ ¬ X
¬¬invol₂ = {!!}

nnlem : {X : Set} → ¬ ¬ (X ⊎ ¬ X)
nnlem f = f (inr (λ x → f (inl x)))

nndnp : {X : Set} → ¬ ¬ (¬ ¬ X → X)
nndnp f = f λ ¬¬x → exfalso (¬¬x λ x → f λ ¬¬x2 → x)

dec2stab : {X : Set} → (X ⊎ ¬ X) → (¬ ¬ X → X)
dec2stab = {!!}

-- you have to decide:
Dec : Set → Set
Dec A = A ⊎ ¬ A

ee1 : {X Y : Set} → Dec (X ⊎ Y → ¬ ¬ (Y ⊎ X))
ee1 = inl λ where (inl x) f → f (inr x)
                  (inr y) f → f (inl y)

ee2 : {X : Set} → Dec (¬ (X ⊎ ¬ X))
ee2 = {!!}

e3 : {X : Set} → Dec (¬ (X → (¬ X → X)))
e3 = {!!}

e4 : Dec ℕ
e4 = {!!}

e5 : Dec ⊥
e5 = {!!}

e6 : {X : Set} → Dec (⊥ → X ⊎ ¬ X)
e6 = {!!}

e7 : {X : Set} → Dec (X × ¬ X → ¬ X ⊎ X)
e7 = {!!}

e8 : {X : Set} → Dec ((X → X) → ⊥)
e8 = {!!}

f1 : {X Y : Set} → ¬ ¬ X ⊎ ¬ ¬ Y → ¬ ¬ (X ⊎ Y)
f1 = {!!}

f2 : ({X Y : Set} → ¬ (X × Y) → ¬ X ⊎ ¬ Y) → {X Y : Set} → ¬ ¬ (X ⊎ Y) → ¬ ¬ X ⊎ ¬ ¬ Y
f2 = {!!}
