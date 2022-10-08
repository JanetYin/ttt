open import lib

---------------------------------------------------------
-- propositional logic
------------------------------------------------------

subt-prod : {A A' B B' : Type} → (A → A') → (B → B') → A × B → A' × B'
subt-prod = {!!}

subt-fun : {A A' B B' : Type} → (A → A') → (B → B') → (A' → B) → (A → B')
subt-fun = {!!}

anything : {X Y : Type} → ¬ X → X → Y
anything = {!!}

ret : {X : Type} → X → ¬ ¬ X
ret = {!!}

fun : {X Y : Type} → (¬ X) ⊎ Y → (X → Y)
fun = {!!}

-- De Morgan

dm1 : {X Y : Type} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
dm1 = {!!}

dm2 : {X Y : Type} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 = {!!}

dm2b : {X Y : Type} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b = {!!}

-- stuff

nocontra : {X : Type} → ¬ (X ↔ ¬ X)
nocontra = {!!}

¬¬invol₁ : {X : Type} → ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
¬¬invol₁ = {!!}

¬¬invol₂ : {X : Type} → ¬ ¬ ¬ X ↔ ¬ X
¬¬invol₂ = {!!}

nnlem : {X : Type} → ¬ ¬ (X ⊎ ¬ X)
nnlem = {!!}

nndnp : {X : Type} → ¬ ¬ (¬ ¬ X → X)
nndnp = {!!}

dec2stab : {X : Type} → (X ⊎ ¬ X) → (¬ ¬ X → X)
dec2stab = {!!}

-- you have to decide:
Dec : Type → Type
Dec A = A ⊎ ¬ A

ee1 : {X Y : Type} → Dec (X ⊎ Y → ¬ ¬ (Y ⊎ X))
ee1 = {!!}

ee2 : {X : Type} → Dec (¬ (X ⊎ ¬ X))
ee2 = {!!}

e3 : {X : Type} → Dec (¬ (X → (¬ X → X)))
e3 = {!!}

e4 : Dec ℕ
e4 = {!!}

e5 : Dec ⊥
e5 = {!!}

e6 : {X : Type} → Dec (⊥ → X ⊎ ¬ X)
e6 = {!!}

e7 : {X : Type} → Dec (X × ¬ X → ¬ X ⊎ X)
e7 = {!!}

e8 : {X : Type} → Dec ((X → X) → ⊥)
e8 = {!!}

f1 : {X Y : Type} → ¬ ¬ X ⊎ ¬ ¬ Y → ¬ ¬ (X ⊎ Y)
f1 = {!!}

f2 : ({X Y : Type} → ¬ (X × Y) → ¬ X ⊎ ¬ Y) → {X Y : Set} → ¬ ¬ (X ⊎ Y) → ¬ ¬ X ⊎ ¬ ¬ Y
f2 = {!!}
