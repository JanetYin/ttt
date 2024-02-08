open import Lib

---------------------------------------------------------
-- propositional logic
------------------------------------------------------

{-
negált : \neg ¬    : A → ⊥
konjunkció (és) : (×)
diszjunkció (vagy) : (⊎)
implikáció : (→)
-}

subt-prod : {A A' B B' : Set} → (A → A') → (B → B') → A × B → A' × B'
subt-prod aa' bb' ab = (aa' (fst ab)) , (bb' (snd ab))

subt-fun : {A A' B B' : Set} → (A → A') → (B → B') → (A' → B) → (A → B')
subt-fun aa' bb' a'b a = bb' (a'b (aa' a))

anything : {X Y : Set} → ¬ X → X → Y
anything x x₁ = exfalso (x x₁)

ret : {X : Set} → X → ¬ (¬ X)
ret x x₁ = x₁ x

fun : {X Y : Set} → (¬ X) ⊎ Y → (X → Y)
fun (inl a) x = exfalso (a x)
fun (inr b) x = b

-- De Morgan

dm1 : {X Y : Set} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
fst dm1 f = (λ x → f (inl x)) , λ y → f (inr y)
snd dm1 (¬x , ¬y) (inl x) = ¬x x
snd dm1 (¬x , ¬y) (inr y) = ¬y y

dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 (inl a) (x , y) = a x
dm2 (inr b) (x , y) = b y

dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b f = f (λ ¬xy → inr λ y → f (λ ¬xy1 → inl λ x → ¬xy (x , y)))

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
ee1 = yes λ where (yes a) → λ x → x (inr a)
                  (no b) → λ x → x (inl b)

ee2 : {X : Set} → Dec (¬ (X ⊎ ¬ X))
ee2 = no λ f → f (no (λ x → f (inl x)))

e3 : {X : Set} → Dec (¬ (X → (¬ X → X)))
e3 = inr λ x → x (λ x₁ x₂ → x₁)

e4 : Dec ℕ
e4 = inl zero

e5 : Dec ⊥
e5 = inr λ x → x

e6 : {X : Set} → Dec (⊥ → X ⊎ ¬ X)
e6 = {!!}

e7 : {X : Set} → Dec (X × ¬ X → ¬ X ⊎ X)
e7 = inl λ where (x , ¬x) → inr x

e8 : {X : Set} → Dec ((X → X) → ⊥)
e8 = {!!}

f1 : {X Y : Set} → ¬ ¬ X ⊎ ¬ ¬ Y → ¬ ¬ (X ⊎ Y)
f1 = {!!}

f2 : ({X Y : Set} → ¬ (X × Y) → ¬ X ⊎ ¬ Y) → {X Y : Set} → ¬ ¬ (X ⊎ Y) → ¬ ¬ X ⊎ ¬ ¬ Y
f2 = {!!}
