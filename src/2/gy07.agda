open import lib

---------------------------------------------------------
-- propositional logic
------------------------------------------------------

subt-prod : {A A' B B' : Set} → (A → A') → (B → B') → A × B → A' × B'
subt-prod af bf (a , b) = af a , bf b

subt-fun : {A A' B B' : Set} → (A → A') → (B → B') → (A' → B) → (A → B')
subt-fun aa' bb' a'b a = bb' (a'b (aa' a))

anything : {X Y : Set} → ¬ X → X → Y
anything ¬x x = exfalso (¬x x)

ret : {X : Set} → X → ¬ ¬ X
ret x ¬x = ¬x x

fun : {X Y : Set} → (¬ X) ⊎ Y → (X → Y)
fun = {!!}

-- De Morgan

dm1 : {X Y : Set} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
fst dm1 x = (λ x₁ → x (inl x₁)) , λ x₁ → x (inr x₁)
snd dm1 (f , g) (inl x) = f x
snd dm1 (f , g) (inr y) = g y

dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 (inl ¬x) (x , y) = ¬x x
dm2 (inr ¬y) (x , y) = ¬y y

dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b f = f λ ¬xy → inl λ x → f λ ¬xy₁ → inr λ y → ¬xy (x , y)

-- stuff

nocontra : {X : Set} → ¬ (X ↔ ¬ X)
nocontra (x¬x , ¬xx) = x¬x (¬xx (λ x → x¬x x x)) (¬xx (λ x → x¬x x x))

¬¬invol₁ : {X : Set} → ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
fst ¬¬invol₁ ¬¬¬¬x ¬x = ¬¬¬¬x λ ¬¬x → ¬¬x ¬x
snd ¬¬invol₁ ¬¬x ¬¬¬x = ¬¬¬x ¬¬x

¬¬invol₂ : {X : Set} → ¬ ¬ ¬ X ↔ ¬ X
fst ¬¬invol₂ ¬¬¬x x = ¬¬¬x λ ¬x → ¬x x
snd ¬¬invol₂ ¬x ¬¬x = ¬¬x ¬x

nnlem : {X : Set} → ¬ ¬ (X ⊎ ¬ X)
nnlem f = f (inr λ x → f (inl x))

nndnp : {X : Set} → ¬ ¬ (¬ ¬ X → X)
nndnp x = x λ ¬¬x → exfalso (¬¬x λ x₁ → x λ x₂ → x₁)

dec2stab : {X : Set} → (X ⊎ ¬ X) → (¬ ¬ X → X)
dec2stab (inl x) ¬¬x = x
dec2stab (inr ¬x) ¬¬x = exfalso (¬¬x ¬x)

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
