module gy07 where

open import Lib

---------------------------------------------------------
-- propositional logic
------------------------------------------------------

subt-prod : {A A' B B' : Set} → (A → A') → (B → B') → A × B → A' × B'
subt-prod f g (a , b) = (f a) , (g b)

subt-fun : {A A' B B' : Set} → (A → A') → (B → B') → (A' → B) → (A → B')
subt-fun f g h a = g (h (f a))

anything : {X Y : Set} → ¬ X → X → Y
anything ¬x x = exfalso (¬x x)

ret : {X : Set} → X → ¬ ¬ X
ret x ¬x = ¬x x

-- \neg = ¬
-- Próbáljuk meg bizonyítani:
{-
stab : {X : Set} → ¬ ¬ X → X
stab ¬¬x = exfalso (¬¬x (λ x → ¬¬x λ x₁ → ¬¬x (λ x₂ → ¬¬x (λ x₃ → NEM FOG MENNI))))
-}
-- Konstruktív logika

fun : {X Y : Set} → (¬ X) ⊎ Y → (X → Y)
fun (inl ¬x) x = contradiction x ¬x -- contradiction x ¬x = exfalso (¬x x)
fun (inr y) x = y

-- De Morgan

dm1 : {X Y : Set} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
fst dm1 ¬xy = (λ x → ¬xy (inl x)) , λ y → ¬xy (inr y)
snd dm1 (¬x , ¬y) (inl x) = ¬x x
snd dm1 (¬x , ¬y) (inr y) = ¬y y

dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 = {!   !}

dm2b : {X Y : Set} → (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b = {!   !}

-- stuff

nocontra : {X : Set} → ¬ (X ↔ ¬ X)
nocontra = {!   !}

¬¬invol₁ : {X : Set} → ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
¬¬invol₁ = {!   !}

¬¬invol₂ : {X : Set} → ¬ ¬ ¬ X ↔ ¬ X
¬¬invol₂ = {!   !}

nnlem : {X : Set} → ¬ ¬ (X ⊎ ¬ X)
nnlem f = f (inr λ x → f (inl x))

nndnp : {X : Set} → ¬ ¬ (¬ ¬ X → X)
nndnp = {!   !}

dec2stab : {X : Set} → (X ⊎ ¬ X) → (¬ ¬ X → X)
dec2stab = {!   !}

-- you have to decide:
{-
Dec : Set → Set
Dec A = A ⊎ ¬ A
-}

open import Lib.Dec.PatternSynonym


-- yes ≡ inl
-- no ≡ inr
ee1 : {X Y : Set} → Dec (X ⊎ Y → ¬ ¬ (Y ⊎ X))
ee1 = yes λ where (inl x) ¬yx → ¬yx (inr x)
                  (inr y) ¬yx → ¬yx (inl y)

ee2 : {X : Set} → Dec (¬ (X ⊎ ¬ X))
ee2 = no nnlem  

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

f1 : {X Y : Set} → ¬ ¬ X ⊎ ¬ ¬ Y → ¬ ¬ (X ⊎ Y)
f1 = {!   !}

f2 : ({X Y : Set} → ¬ (X × Y) → ¬ X ⊎ ¬ Y) → {X Y : Set} → ¬ ¬ (X ⊎ Y) → ¬ ¬ X ⊎ ¬ ¬ Y
f2 = {!   !}
