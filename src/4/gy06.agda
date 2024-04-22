module gy06 where

open import Lib

---------------------------------------------------------
-- propositional logic
------------------------------------------------------

-- Curry-Howard izomorfizmus
-- Elmélet:
--   ∙ átalakítani logikai állításokat típusokra.
--   ∙ formalizálni állításokat típusokkal.
--   × = ∧ = konjunkció
--   ⊎ = ∨ = diszjunkció
--   ¬ = ¬ = negáció
--   ⊃ = → = implikáció


--------------------------------------------------
-- Formalisation
--------------------------------------------------

-- Formalizáljuk a mondatokat!

-- Az egyes formalizált alap mondatrészeket vegyük fel modul paraméterként, akkor szépen fog működni minden.
module Formalise
  (TheSunIsShining : Set)
  (ItsRaining : Set)
  (WeNeedAnUmbrella : Set)
  (Rainbow : Set)
  where

  -- Nem süt a nap.
  form1 : Set -- \neg
  form1 = ¬ TheSunIsShining

  -- Esik az eső és süt a nap.
  form2 : Set
  form2 = TheSunIsShining × ItsRaining

  -- Nem kell az esernyő vagy esik az eső.
  -- We don't need an umbrella or it's raining
  form3 : Set
  form3 = (¬ WeNeedAnUmbrella) ⊎ ItsRaining

  -- Ha esik az eső és süt a nap, akkor van szivárvány.
  -- If it's raining and it's sunny, then there's a rainbow.
  form4 : Set
  form4 = (ItsRaining × TheSunIsShining) → Rainbow

  -- Van szivárvány.
  -- There's a rainbow
  K : Set
  K = Rainbow

---- Következményfogalom (logika tárgy 1-3. gyakorlat)
  -- Agdában legegyszerűbben szintaktikus következményekkel lehet foglalkozni.

  -- Mondd ki, és bizonyítsd be, hogy a fenti állításokból következik a K.
  -- A típusban kell kimondani az állítást; az állítás kimondásához az eldöntésprobléma tételét kell használni.
  -- Két féleképpen lehet bizonyítani.

  Köv : Set
  Köv = (form1 × form2 × form3 × form4) → K

--  C-u C-u C-c C-,
-- form 1: TheSunIsShining → ⊥
-- form 2: TheSunIsShining × ItsRaining
-- form 3: (¬ WeNeedUmbrella) ⊎ ItsRaining
-- form 4: (ItsRaining × TheSunIsShining) → Rainbow
  Köv1 : Köv
  Köv1 (form₁ , form₂ , form₃ , form₄) = exfalso (form₁ (fst form₂))

  Köv2 : Köv
  Köv2 = {!!}

----------------------------------------------------------------------------

wklem : {A : Set} → ¬ ¬ (A ⊎ (¬ A))
wklem ¬[a∨¬a] = ¬[a∨¬a] (inr λ a → ¬[a∨¬a] (inl a))

subt-prod : {A A' B B' : Set} → (A → A') → (B → B') → A × B → A' × B'
subt-prod a→a' b→b' (a , b) = (a→a' a) , (b→b' b)

subt-fun : {A A' B B' : Set} → (A → A') → (B → B') → (A' → B) → (A → B')
subt-fun = {!!}

anything : {X Y : Set} → ¬ X → X → Y
anything = {!!}

ret : {X : Set} → X → ¬ ¬ X
ret = {!!}

fun : {X Y : Set} → (¬ X) ⊎ Y → (X → Y)
fun = {!!}

-- De Morgan

dm1 : {X Y : Set} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
fst (fst dm1 a) x = a (inl x)
snd (fst dm1 a) y = a (inr y)
snd dm1 ¬X×¬Y (inl x) = fst ¬X×¬Y x
snd dm1 ¬X×¬Y (inr y) = snd ¬X×¬Y y

expr₁ : {A B : Set} → (¬ (A → B) → ¬ ¬ A × ¬ B)
fst (expr₁ x) x₁ = x (λ a → exfalso (x₁ a))
snd (expr₁ x) b = x (λ _ → b)

expr₂ : {A B : Set} → ¬ ¬ (¬ (A → B) → A × ¬ B)
expr₂ x = x (λ ¬[a→b] → exfalso (¬[a→b] (λ a → exfalso (x (λ _ → a , (λ b → ¬[a→b] (λ _ → b))))))
          , (λ b → ¬[a→b] (λ _ → b)))

dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 = {!!}

dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b a = {!!}

-- a (λ ¬[x×y] → inl λ x → a (λ _ → inr λ y → ¬[x×y] (x , y)))


wk : {A : Set} → A ⊎ (¬ A)
wk = inr λ a → {!!}

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

----------------------------------------------------------------------
-- Not exactly first order logic but kinda is and kinda isn't.

f3 : Dec ((X Y : Set) → X ⊎ Y → Y)
f3 = {!!}

f4 : Dec ((X Y Z : Set) → (X → Z) ⊎ (Y → Z) → (X ⊎ Y → Z))
f4 = {!!}

f5 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f5 = {!!}

f6 : Dec ((X Y Z : Set) → (X × Y → Z) → (X → Z) × (Y → Z))
f6 = {!!}

f7 : Dec ((X Y Z : Set) → (X ⊎ Y × Z) → (X ⊎ Y) × (X ⊎ Z))
f7 = {!!}

f8 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → ((X ⊎ Y) × Z))
f8 = {!!}

f9 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → (X ⊎ Y × Z))
f9 = {!!}
