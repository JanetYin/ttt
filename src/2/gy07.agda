open import Lib

---------------------------------------------------------
-- propositional logic
------------------------------------------------------

subt-prod : {A A' B B' : Set} → (A → A') → (B → B') → A × B → A' × B'
subt-prod a→a' b→b' a×b = (a→a' (fst a×b)) , b→b' (snd a×b)

subt-fun : {A A' B B' : Set} → (A → A') → (B → B') → (A' → B) → (A → B')
subt-fun = {!!}

anything : {X Y : Set} → ¬ X → X → Y
anything ¬x x = exfalso (¬x x)

ret : {X : Set} → X → ¬ ¬ X
ret x ¬x = ¬x x

-- retback : {X : Set} → ¬ ¬ X → X
-- retback ¬¬x = exfalso (¬¬x (λ x → ¬¬x (λ x₁ → {!!})))

fun : {X Y : Set} → (¬ X) ⊎ Y → (X → Y)
fun (inl ¬x) x = anything ¬x x
fun (inr y) x = y

-- De Morgan

dm1 : {X Y : Set} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
fst (fst dm1 ¬x∪y) x = ¬x∪y (inl x)
snd (fst dm1 ¬x∪y) y = ¬x∪y (inr y)
snd dm1 (¬x , ¬y) (inl x) = ¬x x
snd dm1 (¬x , ¬y) (inr y) = ¬y y

dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 (inl ¬x) (x , y) = ¬x x
dm2 (inr ¬y) (x , y) = ¬y y

dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b ¬[¬x∧y→¬x∪¬y] = ¬[¬x∧y→¬x∪¬y] (λ ¬[x×y] → inl λ x → ¬[x×y] (x , (exfalso (¬[¬x∧y→¬x∪¬y] λ _ → inr λ y → ¬[x×y] (x , y)))))
-- dm2b ¬[¬x∧y→¬x∪¬y] = ¬[¬x∧y→¬x∪¬y] (λ ¬[x×y] → inl λ x → {!!})
-- Step 0: Egy idő után ⊥-ot kell visszaadni
-- Step 1: Végig megyünk az összes ⊥-ba képző fv-en "rekurzívan" és bevezetjük az összes lehetséges információt

-- stuff

nocontra : {X : Set} → ¬ (X ↔ ¬ X)
nocontra (x→¬x , ¬x→x) = x→¬x (¬x→x (λ x → x→¬x x x)) (¬x→x (λ x → x→¬x x x))

¬¬invol₁ : {X : Set} → ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
fst ¬¬invol₁ ¬¬¬¬X ¬X = ¬¬¬¬X (λ ¬¬X → ¬¬X (λ x → ¬X x))
snd ¬¬invol₁ ¬¬X ¬¬¬X = ¬¬¬X ¬¬X

¬¬invol₂ : {X : Set} → ¬ ¬ ¬ X ↔ ¬ X
fst ¬¬invol₂ ¬¬¬x x = ¬¬¬x (λ ¬x → ¬x x)
snd ¬¬invol₂ ¬x ¬¬x = ¬¬x ¬x

nnlem : {X : Set} → ¬ ¬ (X ⊎ ¬ X)
nnlem ¬[x∨¬x] = ¬[x∨¬x] (inr λ x → ¬[x∨¬x] (inl x))

nndnp : {X : Set} → ¬ ¬ (¬ ¬ X → X)
nndnp ¬[¬¬x→x] = ¬[¬¬x→x] (λ ¬¬x → exfalso (¬¬x (λ x → ¬[¬¬x→x] (λ _ → x))))

dec2stab : {X : Set} → (X ⊎ ¬ X) → (¬ ¬ X → X)
dec2stab (inl x) ¬¬x = x
dec2stab (inr ¬x) ¬¬x = exfalso (¬¬x ¬x)

-- you have to decide:
{-
Dec : Set → Set
Dec A = A ⊎ ¬ A
-}

open import Lib.Dec.PatternSynonym

ee1 : {X Y : Set} → Dec (X ⊎ Y → ¬ ¬ (Y ⊎ X))
ee1 = {!!}

ee2 : {X : Set} → Dec (¬ (X ⊎ ¬ X))
ee2 = ?

e3 : {X : Set} → Dec (¬ (X → (¬ X → X)))
e3 = {!!}

e4 : Dec ℕ
e4 = ?

e5 : Dec ⊥
e5 = ?

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
