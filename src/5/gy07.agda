open import lib

---------------------------------------------------------
-- propositional logic
------------------------------------------------------

-- ∧ : ×
-- ∨ : ⊎
-- ⊃ : →
-- ¬ : ¬

-- ¬X : X → ⊥

subt-prod : {A A' B B' : Set} → (A → A') → (B → B') → A × B → A' × B'
subt-prod aa' bb' (a , b) = aa' a , bb' b

subt-fun : {A A' B B' : Set} → (A → A') → (B → B') → (A' → B) → (A → B')
subt-fun aa' bb' a'b a = bb' (a'b (aa' a))

anything : {X Y : Set} → ¬ X → X → Y
anything ¬x x = exfalso (¬x x)

ret : {X : Set} → X → ¬ ¬ X
ret x x₁ = x₁ x

fun : {X Y : Set} → (¬ X) ⊎ Y → (X → Y)
fun (inl x) x₁ = exfalso (x x₁)
fun (inr x) x₁ = x

-- De Morgan

dm1 : {X Y : Set} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
fst dm1 x = (λ x₁ → x (inl x₁)) , λ x₁ → x (inr x₁)
snd dm1 (fst₁ , snd₁) (inl x₁) = fst₁ x₁
snd dm1 (fst₁ , snd₁) (inr x₁) = snd₁ x₁

dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 (inl x) (fst₁ , snd₁) = x fst₁
dm2 (inr x) (fst₁ , snd₁) = x snd₁

dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b x = x λ x₁ → inl λ x₂ → x λ x₃ → inr λ x₄ → x₃ (x₂ , x₄)

-- stuff

nocontra : {X : Set} → ¬ (X ↔ ¬ X)
nocontra (x¬x , ¬xx) = x¬x (¬xx (λ x → x¬x x x)) (¬xx λ x → x¬x x x)

¬¬invol₁ : {X : Set} → ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
fst ¬¬invol₁ x x₁ = x λ x₂ → x₂ x₁
snd ¬¬invol₁ x x₁ = x₁ x

¬¬invol₂ : {X : Set} → ¬ ¬ ¬ X ↔ ¬ X
fst ¬¬invol₂ x x₁ = x λ x₂ → x₂ x₁
snd ¬¬invol₂ x x₁ = x₁ x

nnlem : {X : Set} → ¬ ¬ (X ⊎ ¬ X)
nnlem x = x (inr λ x₁ → x (inl x₁))

nndnp : {X : Set} → ¬ ¬ (¬ ¬ X → X)
nndnp x = x λ x₁ → exfalso (x₁ λ x₂ → x λ x₃ → x₂)

dec2stab : {X : Set} → (X ⊎ ¬ X) → (¬ ¬ X → X)
dec2stab (inl x) x₁ = x
dec2stab (inr x) x₁ = exfalso (x₁ x)

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
