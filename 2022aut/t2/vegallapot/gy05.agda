open import lib

---------------------------------------------------------
-- propositional logic
------------------------------------------------------

subt-prod : {A A' B B' : Set} → (A → A') → (B → B') → A × B → A' × B'
subt-prod a→a' b→b' = λ axb → a→a' (fst axb) , b→b' (snd axb)

--homework
subt-fun : {A A' B B' : Set} → (A → A') → (B → B') → (A' → B) → (A → B') --drawing?
subt-fun = {!!}


anything : {X Y : Set} → ¬ X → X → Y    --\neg
anything nx x = exfalso (nx x)

ret : {X : Set} → X → ¬ ¬ X
ret x = λ nx → nx x


-- however, it's not true by default the other way round
-- constructive logics (Brouwer)
{-
-- tertium non datur
tnd : {X : Set} → X ⊎ ¬ X         --also lem (law of the excluded middle)
tnd = ?

tnd is usually not true in Agda: constructive mathematics
-}

{-
you can still assume it's true:
postulate
  tnd : {X : Set} → X ⊎ ¬ X
-}

fun : {X Y : Set} → (¬ X) ⊎ Y → (X → Y)
fun nxvy = λ x → case nxvy (λ nx → (exfalso (nx x))) λ y → y

-- De Morgan

--homework
dm1 : {X Y : Set} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
dm1 = (λ n[xvy] → (λ x → n[xvy] (inl x)) , λ y → n[xvy] (inr y)) , (λ (nx , ny) → λ xvy → case xvy nx ny)

--homework
dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 = λ nxvny → case nxvny (λ nx → λ xay → nx (fst xay)) λ ny → λ xay → ny (snd xay)



-- without ¬ ¬, it would need tnd
dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b = λ s → s λ ¬[x×y] → inl λ x → s λ _ → inr λ y → ¬[x×y] (x , y)           --climb into ¬x and ¬y so that you have an x and y, and then derive a contradiction


-- stuff

--homework
nocontra : {X : Set} → ¬ (X ↔ ¬ X)
nocontra = {!!}

-- special cases where ¬ ¬ A → A is true:
¬¬invol₁ : {X : Set} → ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
¬¬invol₁ =  (λ nnnnx → λ nx → nnnnx λ nnx → nnx nx)
             , ret     --C-c C-z

-- homework
¬¬invol₂ : {X : Set} → ¬ ¬ ¬ X ↔ ¬ X
¬¬invol₂ = {!!}


nntnd : {X : Set} → ¬ ¬ (X ⊎ ¬ X)
nntnd = {!!}
-- another one with de Morgan

-- double negation principle
-- dnp is the basis of proofs by contradiction
-- it is not provable either, only ¬ ¬ dnp
nndnp : {X : Set} → ¬ ¬ (¬ ¬ X → X)
nndnp = λ s → s λ nnx → exfalso (nnx λ x → s λ _ → x)        --C-u C-u C-c C-,

-- homework
-- actually, tnd would imply dnp
tnd2dnp : {X : Set} → (X ⊎ ¬ X) → (¬ ¬ X → X)
tnd2dnp = λ tnd → case tnd (λ x _ → x) λ nx nnx → exfalso (nnx nx)

Dec : Set → Set
Dec A = A ⊎ ¬ A
--now this means you have to decide whether it's true or not

{-
dectnd : {X : Set} → Dec (X ⊎ ¬ X)
dectnd = {!!} --this does not have an element
--}

ee1 : {X Y : Set} → Dec (X ⊎ Y → ¬ ¬ (Y ⊎ X))   --is it true that...
ee1 = inl (λ xvy → λ n[yvx] → n[yvx] (case xvy inr inl))

--homework
ee2 : {X : Set} → Dec (¬ (X ⊎ ¬ X)) --hint: use earlier one
ee2 = {!!}

--homework
e3 : {X : Set} → Dec (¬ (X → (¬ X → X)))
e3 = {!!}

--homework
e4 : Dec ℕ    -- it also accepts other types
e4 = {!!}

--homework
e5 : Dec ⊥
e5 = {!!}

--homework
e6 : {X : Set} → Dec (⊥ → X ⊎ ¬ X)
e6 = {!!}

--homework
e7 : {X : Set} → Dec (X × ¬ X → ¬ X ⊎ X)
e7 = {!!}

e8 : {X : Set} → Dec ((X → X) → ⊥)
e8 = inr λ f → f (λ x → x)

f1 : {X Y : Set} → ¬ ¬ X ⊎ ¬ ¬ Y → ¬ ¬ (X ⊎ Y)
f1 = {!!}

f2 : ({X Y : Set} → ¬ (X × Y) → ¬ X ⊎ ¬ Y) → {X Y : Set} → ¬ ¬ (X ⊎ Y) → ¬ ¬ X ⊎ ¬ ¬ Y
f2 = {!!}

{-
for dm2b:
λ f → f λ nxay →  inl λ x → f λ _ → inr λ y → nxay (x , y)
-}
