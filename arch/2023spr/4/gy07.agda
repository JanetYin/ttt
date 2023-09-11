open import lib

---------------------------------------------------------
-- propositional logic
------------------------------------------------------

-- C-c C-,               sima
-- C-u C-c C-,           absztraktok figyelmen kívül hagyása
-- C-u C-u C-c C-,       feloldja a rövidítéseket
-- pontokkal ugyanezek   kiírja azt is, hogy te milyen típusú dolgot írtál bele
-- C-c C-z               keresés a definíciók között

subt-prod : {A A' B B' : Set} → (A → A') → (B → B') → A × B → A' × B'
subt-prod = {!!}

subt-fun : {A A' B B' : Set} → (A → A') → (B → B') → (A' → B) → (A → B')
subt-fun = {!!}

anything : {X Y : Set} → ¬ X → X → Y      -- \neg
anything nx x = {!!}

-- ¬ ¬ X = (¬ X) → ⊥ = (X → ⊥) → ⊥
ret : {X : Set} → X → ¬ ¬ X     -- X → (X → ⊥) → ⊥
ret x nx = nx x

fun : {X Y : Set} → (¬ X) ⊎ Y → (X → Y)
fun = {!!}

-- De Morgan

dm1 : {X Y : Set} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
dm1 = {!!}

dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 = {!!}

dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b t = t λ nxay → inl λ x → t λ _ → inr λ y → nxay (x , y)
-- minek a ¬ ¬?

-- dolgok:

nocontra : {X : Set} → ¬ (X ↔ ¬ X)
nocontra = {!!}

¬¬invol₁ : {X : Set} → ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
¬¬invol₁ = {!!}

¬¬invol₂ : {X : Set} → ¬ ¬ ¬ X ↔ ¬ X
fst ¬¬invol₂ nnnx = λ x → nnnx λ nx → nx x
snd ¬¬invol₂ = {!!}

nnlem : {X : Set} → ¬ ¬ (X ⊎ ¬ X)
nnlem n[xvnx] = n[xvnx] (inr λ x → n[xvnx] (inl x))

nndnp : {X : Set} → ¬ ¬ (¬ ¬ X → X)
nndnp = {!!}

-- ezeket együtt majd

-- kizárt harmadik elve (law of excluded middle, tertium non datur)
lem : {X : Set} → X ⊎ ¬ X
lem = inr {!!}
-- nem lehet bizonyítani

dnp : {X : Set} → ¬ ¬ X → X
dnp nnx = {!!}
-- ezt sem lehet

lem→dnp : {X : Set} → (X ⊎ ¬ X) → (¬ ¬ X → X)
lem→dnp = {!!}

-- ez azt jelenti, hogy neked kell már eldönteni, hogy
-- azt bizonyítod, hogy van-e eleme, vagy azt, hogy nincs
Dec : Set → Set
Dec A = A ⊎ ¬ A

-----------------------------------------------------------
-- házi
ee1 : {X Y : Set} → Dec (X ⊎ Y → ¬ ¬ (Y ⊎ X))
ee1 = inl λ xvy → λ nyvx → nyvx (case xvy (λ x → inr x) λ y → inl y)

ee2 : {X : Set} → Dec (¬ (X ⊎ ¬ X))
ee2 = {!!}

e3 : {X : Set} → Dec (¬ (X → (¬ X → X)))
e3 = {!!}

e4 : Dec ℕ
e4 = inl 5

e5 : Dec ⊥
e5 = inr λ ()

e6 : {X : Set} → Dec (⊥ → X ⊎ ¬ X)
e6 = inl λ ()

e7 : {X : Set} → Dec (X × ¬ X → ¬ X ⊎ X)
e7 = {!!}

e8 : {X : Set} → Dec ((X → X) → ⊥)
e8 = {!!}

-----------------------------------------------------------
-- itteni
f1 : {X Y : Set} → ¬ ¬ X ⊎ ¬ ¬ Y → ¬ ¬ (X ⊎ Y)
f1 nnxvnny = λ n[xvy] → case nnxvnny (λ nnx → nnx λ x → n[xvy] (inl x))
                                       λ nny → nny λ y → n[xvy] (inr y)

f2 : ({A B : Set} → ¬ (A × B) → ¬ A ⊎ ¬ B) → {X Y : Set} → ¬ ¬ (X ⊎ Y) → ¬ ¬ X ⊎ ¬ ¬ Y
f2 hyp {X} {Y} nn[xvy] = hyp λ nxany → nn[xvy] λ xvy → case xvy (fst nxany) (snd nxany)
