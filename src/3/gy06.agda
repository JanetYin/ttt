module gy06 where

open import Lib

----------------------------------------------
-- Some Sigma types
----------------------------------------------

Σ=⊎ : {A B : Set} → Σ Bool (if_then A else B) ↔ A ⊎ B
fst Σ=⊎ (false , sn) = inr sn
fst Σ=⊎ (true , sn) = inl sn
snd Σ=⊎ (inl a) = true , a
snd Σ=⊎ (inr b) = false , b

Σ=× : {A B : Set} → Σ A (λ _ → B) ↔ A × B
fst Σ=× (fs , sn) = fs , sn
snd Σ=× = id

-- Π A F is essentially (a : A) → F a
-- what does this mean?

                    -- Π A (λ _ → B)
Π=→ : {A B : Set} → ((a : A) → (λ _ → B) a) ≡ (A → B)
Π=→ = refl

                    -- Π Bool (if_then A else B)
→=× : {A B : Set} → ((b : Bool) → if b then A else B) ↔ A × B
fst →=× x = (x true) , (x false)
snd →=× x false = snd x
snd →=× x true = fst x

dependentCurry : {A : Set}{B : A → Set}{C : (a : A) → B a → Set} →
  ((a : A)(b : B a) → C a b) ↔ ((w : Σ A B) → C (fst w) (snd w))
fst dependentCurry x w = x (fst w) (snd w)
snd dependentCurry x a b = x (a , b)

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

subt-prod : {A A' B B' : Set} → (A → A') → (B → B') → A × B → A' × B'
subt-prod f g x = f (fst x) , g (snd x)

subt-fun : {A A' B B' : Set} → (A → A') → (B → B') → (A' → B) → (A → B')
subt-fun f g h a = g (h (f a))

anything : {X Y : Set} → ¬ X → X → Y
anything x y = exfalso (x y)

ret : {X : Set} → X → ¬ ¬ X
ret x f = f x

-- ¬ ¬ X = (¬ X) → ⊥ = (X → ⊥) → ⊥

fun : {X Y : Set} → (¬ X) ⊎ Y → (X → Y)
fun (inl a) y = exfalso (a y)
fun (inr b) y = b

-- De Morgan

dm1 : {X Y : Set} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
fst dm1 x = (λ h → x (inl h)) , λ h → x (inr h)
snd dm1 x (inl a) = fst x a
snd dm1 x (inr b) = snd x b

dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 (inl a) v = a (fst v)
dm2 (inr b) v = b (snd v)

dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b x = x (λ f → inl λ g → x (λ _ → inr λ y → f (g , y)))

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
dec2stab (inl a) x₁ = a
dec2stab (inr b) x₁ = exfalso (x₁ b)

-- you have to decide:
{-
Dec : Set → Set
Dec A = A ⊎ ¬ A
-}

open import Lib.Dec.PatternSynonym

ee1 : {X Y : Set} → Dec (X ⊎ Y → ¬ ¬ (Y ⊎ X))
ee1 {X} {Y} = yes f where
  f : X ⊎ Y → ¬ (¬ (Y ⊎ X))
  f (yes a) x₁ = x₁ (no a)
  f (no b) x₁ = x₁ (yes b)

ee2 : {X : Set} → Dec (¬ (X ⊎ ¬ X))
ee2 = no λ x → x (no (λ y → x (inl y)))

e3 : {X : Set} → Dec (¬ (X → (¬ X → X)))
e3 = no (λ f → f (λ x _ → x))

e4 : Dec ℕ
e4 = yes 42

e5 : Dec ⊥
e5 = no id

e6 : {X : Set} → Dec (⊥ → X ⊎ ¬ X)
e6 = yes exfalso

e7 : {X : Set} → Dec (X × ¬ X → ¬ X ⊎ X)
e7 = yes (λ x → yes (snd x))

e8 : {X : Set} → Dec ((X → X) → ⊥)
e8 = no (λ x → x id)

f1 : {X Y : Set} → ¬ ¬ X ⊎ ¬ ¬ Y → ¬ ¬ (X ⊎ Y)
f1 (yes a) f = a (λ x → f (inl x))
f1 (no b) f = b (λ x → f (inr x))

f2 : ({X Y : Set} → ¬ (X × Y) → ¬ X ⊎ ¬ Y) → {X Y : Set} → ¬ ¬ (X ⊎ Y) → ¬ ¬ X ⊎ ¬ ¬ Y
f2 x {X} {Y} y = x { X → ⊥} {Y → ⊥} λ b → y (λ h → case h (fst b) (snd b)) 
-- yes (λ b → y (λ v → case v b λ h → {!   !}))

----------------------------------------------------------------------
-- Not exactly first order logic but kinda is and kinda isn't.

f3 : Dec ((X Y : Set) → X ⊎ Y → Y)
f3 = no (λ f → f ⊤ _ (inl tt))

f4 : Dec ((X Y Z : Set) → (X → Z) ⊎ (Y → Z) → (X ⊎ Y → Z))
f4 = no (λ f → f ⊤ ⊥ _ (no id) (inl tt))

f5 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f5 = {!!}

f6 : Dec ((X Y Z : Set) → (X × Y → Z) → (X → Z) × (Y → Z))
f6 = no (λ f → (snd (f ⊥ ⊤ _ fst )) tt)

f7 : Dec ((X Y Z : Set) → (X ⊎ Y × Z) → (X ⊎ Y) × (X ⊎ Z))
f7 = {!!}

f8 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → ((X ⊎ Y) × Z))
f8 = {!!}

f9 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → (X ⊎ Y × Z))
f9 = {!!}
  