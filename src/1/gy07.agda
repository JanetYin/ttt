module gy07 where

open import Lib

---------------------------------------------------------
-- propositional logic
---------------------------------------------------------

-- Curry-Howard izomorfizmus
-- Elmélet:
--   ∙ átalakítani logikai állításokat típusokra.
--   ∙ formalizálni állításokat típusokkal.
--   × = ∧ = konjunkció
--   ⊎ = ∨ = diszjunkció
--   ¬ = ¬ = negáció
--   → = ⊃ = implikáció

--------------------------------------------------
-- Formalisation
--------------------------------------------------

-- Formalizáljuk a mondatokat!

-- Az egyes formalizált alap mondatrészeket vegyük fel modul paraméterként, akkor szépen fog működni minden.
module Formalise (S E Ke Sz : Set) where

  -- Nem süt a nap.
  form1 : Set
  form1 = ¬ S -- \neg = ¬

  -- Esik az eső és süt a nap.
  form2 : Set
  form2 = E × S

  -- Nem kell az esernyő vagy esik az eső.
  form3 : Set
  form3 = ¬ Ke ⊎ E

  -- Ha esik az eső és süt a nap, akkor van szivárvány.
  form4 : Set
  form4 = E × S → Sz

  -- Van szivárvány.
  K : Set
  K = Sz

  ---- Következményfogalom (logika tárgy 1-3. gyakorlat)
  -- Agdában legegyszerűbben szintaktikus következményekkel lehet foglalkozni.

  -- Mondd ki, és bizonyítsd be, hogy a fenti állításokból következik a K.
  -- A típusban kell kimondani az állítást; az állítás kimondásához az eldöntésprobléma tételét kell használni.
  -- Két féleképpen lehet bizonyítani.

  Köv : Set
  Köv = form1 → form2 → form3 → form4 → K

  Köv1 : Köv
  Köv1 ¬s e∧s ¬ke∨e e∧s→sz = exfalso (¬s (snd e∧s))

  Köv2 : Köv
  Köv2 ¬s e∧s ¬ke∨e e∧s→sz = e∧s→sz e∧s

--------------------------------------------------

subt-prod : {A A' B B' : Set} → (A → A') → (B → B') → A × B → A' × B'
subt-prod x x₁ x₂ = (x (fst x₂)) , (x₁ (snd x₂))

subt-fun : {A A' B B' : Set} → (A → A') → (B → B') → (A' → B) → (A → B')
subt-fun x x₁ x₂ x₃ = x₁ (x₂ (x x₃))

anything : {X Y : Set} → ¬ X → X → Y
anything ¬x x = exfalso (¬x x)

ret : {X : Set} → X → ¬ ¬ X
ret x f = f x

-- Másik irány?
{-
otherway : {X : Set} → ¬ ¬ X → X
otherway f = exfalso (f λ x → f λ x2 → f λ x3 → {!!})
-}

fun : {X Y : Set} → (¬ X) ⊎ Y → (X → Y)
fun x x₁ = case x (λ x₂ → exfalso (x₂ x₁)) (λ x₂ → x₂)

-- De Morgan

dm1 : {X Y : Set} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
fst dm1 x = (λ x₁ → x (inl x₁)) , (λ x₁ → x (inr x₁))
snd dm1 x x₁ = case x₁ (λ x₂ → fst x x₂) (λ x₂ → snd x x₂)

dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 (inl a) x₁ = a (fst x₁)
dm2 (inr b) x₁ = b (snd x₁)

dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b x = x (λ x₁ → inl λ x₂ → x (λ x₃ → inr λ x₄ → x₁ (x₂ , x₄)))

-- stuff

nocontra : {X : Set} → ¬ (X ↔ ¬ X)
nocontra f = let x = snd f λ x1 → fst f x1 x1 in fst f x x

¬¬invol₁ : {X : Set} → ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
fst ¬¬invol₁ x x₁ = x (λ x₂ → x₂ x₁)
snd ¬¬invol₁ x x₁ = x₁ x

¬¬invol₂ : {X : Set} → ¬ ¬ ¬ X ↔ ¬ X
fst ¬¬invol₂ x x₁ = x (λ x₂ → x₂ x₁)
snd ¬¬invol₂ x x₁ = x₁ x

nnlem : {X : Set} → ¬ ¬ (X ⊎ ¬ X)
nnlem f = f (inr λ x → f (inl x))

nndnp : {X : Set} → ¬ ¬ (¬ ¬ X → X)
nndnp x = x (λ x₁ → exfalso (x₁ (λ x₂ → x (λ x₃ → x₂))))

dec2stab : {X : Set} → (X ⊎ ¬ X) → (¬ ¬ X → X)
dec2stab x x₁ = case x (λ x₂ → x₂) (λ x₂ → exfalso (x₁ x₂))
-- you have to decide:
{-
Dec : Set → Set
Dec A = A ⊎ ¬ A
-}

open import Lib.Dec.PatternSynonym

ee1 : {X Y : Set} → Dec (X ⊎ Y → ¬ ¬ (Y ⊎ X))
ee1 = yes (λ x x₁ → x₁ (case x (λ x₂ → no x₂) λ x₂ → yes x₂))

noee2 : {X : Set} → ¬ (¬ (X ⊎ ¬ X) )
noee2 x = x (no (λ x₁ → x (yes x₁))) 

ee2 : {X : Set} → Dec (¬ (X ⊎ ¬ X))
ee2 = no noee2

e3 : {X : Set} → Dec (¬ (X → (¬ X → X)))
e3 = no λ x → x (λ x₁ x₂ → x₁)

e4 : Dec ℕ
e4 = yes zero

e5 : Dec ⊥
e5 = no (λ {()})

e6 : {X : Set} → Dec (⊥ → X ⊎ ¬ X)
e6 = yes λ x → exfalso x

e7 : {X : Set} → Dec (X × ¬ X → ¬ X ⊎ X)
e7 = yes (λ x → no (fst x))

e8 : {X : Set} → Dec ((X → X) → ⊥)
e8 {X₁} = no λ x → x (λ x₁ → x₁)

f1 : {X Y : Set} → ¬ ¬ X ⊎ ¬ ¬ Y → ¬ ¬ (X ⊎ Y)
f1 (yes a) x₁ = a (λ x → x₁ (yes x))
f1 (no b) x₁ = b (λ x → x₁ (no x))

f2 : ({X Y : Set} → ¬ (X × Y) → ¬ X ⊎ ¬ Y) → {X Y : Set} → ¬ ¬ (X ⊎ Y) → ¬ ¬ X ⊎ ¬ ¬ Y --make use of all the pred
f2 x {X} {Y} x₁ = x (λ x₂ → x₁ (λ x₃ → case x₃ (fst x₂) (snd x₂)))

----------------------------------------------------------------------
-- Not exactly first order logic but kinda is and kinda isn't.
no3 : ¬ ((X Y : Set) → X ⊎ Y → Y )
no3 x with x X Y p1 
  where 
    X Y : Set
    X = ⊤ 
    Y = ⊥
    p1 : X ⊎ Y 
    p1 = yes tt
... | ()
f3 : Dec ((X Y : Set) → X ⊎ Y → Y)
f3 = no no3 

no4 : ¬ ((X Y Z : Set) → (X → Z) ⊎ (Y → Z) → (X ⊎ Y → Z))
no4 x with x X Y Z a1 a2
  where 
    X Y Z : Set
    X = ⊤ 
    Y = ⊥
    Z = ⊥
    a1 : (X → Z) ⊎ (Y → Z)
    a1 = no λ {()} 
    a2 : X ⊎ Y 
    a2 = yes tt
... | ()
f4 : Dec ((X Y Z : Set) → (X → Z) ⊎ (Y → Z) → (X ⊎ Y → Z))
f4 = no no4 

f5 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f5 = yes (λ X Y Z x x₁ → fst x (fst x₁))


no6 : ¬ ((X Y Z : Set) → (X × Y → Z) → (X → Z) × (Y → Z) )
no6 x with x X Y Z p1
  where 
   X Y Z : Set 
   X = ⊤
   Y = ⊥
   Z = ⊥
   p1 : X × Y → Z 
   p1 (x , ()) 
... | fst₁ , snd₁ = fst₁ tt

f6 : Dec ((X Y Z : Set) → (X × Y → Z) → (X → Z) × (Y → Z))
f6 = no no6

f7 : Dec ((X Y Z : Set) → (X ⊎ Y × Z) → (X ⊎ Y) × (X ⊎ Z))
f7 = yes (λ {X Y Z (yes a) → (yes a) , (yes a)
           ; X Y Z (no b) → (no (fst b)) , (no (snd b))})

no8 : ¬ ( (X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → ((X ⊎ Y) × Z) )
no8 x with x X Y Z a1 
  where 
    X : Set 
    X = ⊤
    Y : Set 
    Y = ⊤ 
    Z : Set 
    Z = ⊥
    a1 : (X ⊎ Y) × (X ⊎ Z)
    a1 = yes tt , yes tt
... | ()
f8 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → ((X ⊎ Y) × Z))
f8 = no λ x → no8 x

f9 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → (X ⊎ Y × Z))
f9 = yes p1
  where
    p1 :   (X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → X ⊎ Y × Z 
    p1 X Y Z (yes a , x+z) = yes a
    p1 X Y Z (no b , yes a) = yes a       
    p1 X Y Z (no b , no b₁) = no (b , b₁)      