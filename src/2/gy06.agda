module gy06 where

open import Lib.Sigma
open import Lib.Sum
open import Lib.Bool
open import Lib.Equality
open import Lib.Empty
open import Lib.Nat
open import Lib.Dec

----------------------------------------------
-- Some Sigma types
----------------------------------------------

Σ=⊎ : {A B : Set} → Σ Bool (if_then A else B) ↔ A ⊎ B
fst Σ=⊎ (false , ab) = inr ab
fst Σ=⊎ (true , ab) = inl ab
snd Σ=⊎ (inl a) = true , a
snd Σ=⊎ (inr b) = false , b

Σ=× : {A B : Set} → Σ A (λ _ → B) ↔ A × B
fst Σ=× (a , b) = a , b
snd Σ=× (a , b) = a , b

-- Π A F is essentially (a : A) → F a
-- what does this mean?

                    -- Π A (λ _ → B)
Π=→ : {A B : Set} → ((a : A) → (λ _ → B) a) ≡ (A → B)
Π=→ = refl

                    -- Π Bool (if_then A else B)
→=× : {A B : Set} → ((b : Bool) → if b then A else B) ↔ A × B
fst →=× f = f true , f false
snd →=× (a , b) false = b
snd →=× (a , b) true = a

dependentCurry : {A : Set}{B : A → Set}{C : (a : A) → B a → Set} →
  ((a : A)(b : B a) → C a b) ↔ ((w : Σ A B) → C (fst w) (snd w))
fst dependentCurry f (a , b) = f a b
snd dependentCurry f a b = f (a , b)

---------------------------------------------------------
-- propositional logic
------------------------------------------------------

-- Curry-Howard izomorfizmus
-- Elmélet:
--   ∙ átalakítani logikai állításokat típusokra.
--   ∙ formalizálni állításokat típusokkal.
--   × = ∧ = konjunkció
--   ⊎ = ∨ = diszjunkció
--   ¬ = ¬ = negáció (¬ : {A : Set} → A → ⊥)
--   ⊃ = → = implikáció

--------------------------------------------------
-- Formalisation
--------------------------------------------------

-- Formalizáljuk a mondatokat!

-- Az egyes formalizált alap mondatrészeket vegyük fel modul paraméterként, akkor szépen fog működni minden.
module Formalise {A B C D : Set} where

  {-
  A - Süt a nap.
  B - Esik az eső.
  C - Kell az esernyő.
  D - Van szivárvány.
  -}
  -- Nem süt a nap.
  form1 : Set
  form1 = ¬ A

  -- Esik az eső és süt a nap.
  form2 : Set
  form2 = A × B

  -- Nem kell az esernyő vagy esik az eső.
  form3 : Set
  form3 = ¬ C ⊎ B

  -- Ha esik az eső és süt a nap, akkor van szivárvány.
  form4 : Set
  form4 = (B × A) → D

  -- Van szivárvány.
  K : Set
  K = D

---- Következményfogalom (logika tárgy 1-3. gyakorlat)
  -- Agdában legegyszerűbben szintaktikus következményekkel lehet foglalkozni.

  -- Mondd ki, és bizonyítsd be, hogy a fenti állításokból következik a K.
  -- A típusban kell kimondani az állítást; az állítás kimondásához az eldöntésprobléma tételét kell használni.
  -- Két féleképpen lehet bizonyítani.

  Köv : Set
  Köv = (form1 × form2 × form3 × form4) → K

  Köv1 : Köv
  Köv1 (f1 , f2 , f3 , f4) = f4 (snd f2 , fst f2)

  Köv2 : Köv
  Köv2 (f1 , f2 , f3 , f4) = exfalso (f1 (fst f2))

----------------------------------------------------------------------------

subt-prod : {A A' B B' : Set} → (A → A') → (B → B') → A × B → A' × B'
subt-prod aa' bb' (a , b) = aa' a , bb' b

subt-fun : {A A' B B' : Set} → (A → A') → (B → B') → (A' → B) → (A → B')
subt-fun aa' bb' a'b a = bb' (a'b (aa' a))

anything : {X Y : Set} → ¬ X → X → Y
anything ¬x x = exfalso (¬x x)

ret : {X : Set} → X → ¬ ¬ X
ret x ¬x = ¬x x

fun : {X Y : Set} → (¬ X) ⊎ Y → (X → Y)
fun (inl ¬x) x = anything ¬x x
fun (inr y) x = y

-- De Morgan

dm1 : {X Y : Set} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
fst dm1 ¬xy = (λ x → ¬xy (inl x)) , λ y → ¬xy (inr y)
snd dm1 (¬x , ¬y) (inl x) = ¬x x
snd dm1 (¬x , ¬y) (inr y) = ¬y y

dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 (inl ¬x) (x , y) = ¬x x
dm2 (inr ¬y) (x , y) = ¬y y

dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b f = f λ ¬xy → inl λ x → f λ ¬xy₁ → inr λ y → ¬xy (x , y)

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
ee1 = inl λ where (inl x) x₁ → x₁ (inr x)
                  (inr y) x₁ → x₁ (inl y)

ee2 : {X : Set} → Dec (¬ (X ⊎ ¬ X))
ee2 = inr λ f → f (inr λ x → f (inl x))

e3 : {X : Set} → Dec (¬ (X → (¬ X → X)))
e3 = inr λ f → f λ x ¬x → x

e4 : Dec ℕ
e4 = inl zero

e5 : Dec ⊥
e5 = inr λ x → x

e6 : {X : Set} → Dec (⊥ → X ⊎ ¬ X)
e6 = inl λ x → inl (exfalso x)

e7 : {X : Set} → Dec (X × ¬ X → ¬ X ⊎ X)
e7 = inl λ where (x , ¬x) → inr x

e8 : {X : Set} → Dec ((X → X) → ⊥)
e8 = inr λ f → f λ x → x

f1 : {X Y : Set} → ¬ ¬ X ⊎ ¬ ¬ Y → ¬ ¬ (X ⊎ Y)
f1 (inl a) x₁ = a λ x → x₁ (inl x)
f1 (inr b) x₁ = b λ y → x₁ (inr y)

f2 : ({X Y : Set} → ¬ (X × Y) → ¬ X ⊎ ¬ Y) → {X Y : Set} → ¬ ¬ (X ⊎ Y) → ¬ ¬ X ⊎ ¬ ¬ Y
f2 = {!!}

----------------------------------------------------------------------
-- Not exactly first order logic but kinda is and kinda isn't.

f3 : Dec ((X Y : Set) → X ⊎ Y → Y)
f3 = inr λ f → f ⊤ ⊥ (inl tt)

f4 : Dec ((X Y Z : Set) → (X → Z) ⊎ (Y → Z) → (X ⊎ Y → Z))
f4 = inr λ f → f ⊥ ⊤ ⊥ (inl (λ x → x)) (inr tt)

f5 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f5 = inl λ X Y Z (xz , yz) (x , y) → yz y

f6 : Dec ((X Y Z : Set) → (X × Y → Z) → (X → Z) × (Y → Z))
f6 = inr λ f → snd (f ⊥ ⊤ ⊥ λ x → fst x) tt

f7 : Dec ((X Y Z : Set) → (X ⊎ Y × Z) → (X ⊎ Y) × (X ⊎ Z))
f7 = inl λ where X Y Z (yes x) → inl x , inl x
                 X Y Z (no (y , z)) → inr y , inr z

f8 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → ((X ⊎ Y) × Z))
f8 = inr λ f → snd (f ⊤ ⊤ ⊥ (inl tt , inl tt))

f9 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → (X ⊎ Y × Z))
f9 = inl λ where X Y Z (yes a , yes a₁) → inl a
                 X Y Z (yes a , no b) → inl a
                 X Y Z (no b , yes a) → inl a
                 X Y Z (no b , no b₁) → inr (b , b₁)
 