open import lib

---------------------------------------------------------
-- propositional logic
------------------------------------------------------

-- ∧ = ×
-- v = ⊎
-- ⊃ = →
-- ¬ A = A → ⊥

subt-prod : {A A' B B' : Set} → (A → A') → (B → B') → A × B → A' × B'
subt-prod a→a' b→b' (a , b) = (a→a' a) , (b→b' b)

subt-fun : {A A' B B' : Set} → (A → A') → (B → B') → (A' → B) → (A → B')
subt-fun a→a' b→b' a'→b a = b→b' (a'→b (a→a' a))

anything : {X Y : Set} → ¬ X → X → Y
anything ¬x x = exfalso (¬x x)


ret : {X : Set} → X → ¬ ¬ X
ret x = λ ¬x → ¬x x

fun : {X Y : Set} → (¬ X) ⊎ Y → (X → Y)
fun (inl ¬x) x = anything ¬x x
fun (inr y) _ = y

-- De Morgan

dm1 : {X Y : Set} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
dm1 = (λ ¬x⊎y → (λ x → ¬x⊎y (inl x)) , λ y → ¬x⊎y (inr y)) , λ {
  ¬x×¬y (inl x) → fst ¬x×¬y x ;
  ¬x×¬y (inr y) → snd ¬x×¬y y}

dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 (inl ¬x) (x , y) = ¬x x
dm2 (inr ¬y) (x , y) = ¬y y

dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b f = f (λ ¬x×y →
  inl (λ x → f (λ _ →
  inr (λ y → ¬x×y (x , y)))))

-- stuff

nocontra : {X : Set} → ¬ (X ↔ ¬ X)
nocontra (x→¬x , ¬x→x) = x→¬x (¬x→x (λ x → x→¬x x x)) ((¬x→x (λ x → x→¬x x x)))

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
Dec : Set → Set
Dec A = A ⊎ ¬ A

ee1 : {X Y : Set} → Dec (X ⊎ Y → ¬ ¬ (Y ⊎ X))
ee1 = {!!}

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
