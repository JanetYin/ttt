module gy6 where

open import lib

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

⊎×-distr : X ⊎ (Y × Z) ↔ (X ⊎ Y) × (X ⊎ Z)
⊎×-distr = {!!}

iso : Bool ↔ (⊤ ⊎ ⊤) 
iso = {!!}

-- Testing
idBool : Bool → Bool
idBool = λ b → b
id⊤⊤ : ⊤ ⊎ ⊤ → ⊤ ⊎ ⊤
id⊤⊤ = λ t → t
 
--test1 : (proj₁ iso) (proj₂ iso) ≡ id⊤⊤
test1 : Bool → Bool
test1 = λ b → (proj₂ iso) ((proj₁ iso) b)
test2t : test1 true ≡ idBool true
test2t = refl
test2f : test1 false ≡ idBool false
test2f = refl
test3 : ⊤ ⊎ ⊤ → ⊤ ⊎ ⊤
test3 = λ t → (proj₁ iso) ((proj₂ iso) t)
test41 : test3 (inj₁ tt) ≡ id⊤⊤ (inj₁ tt)
test41 = refl
test42 : test3 (inj₂ tt) ≡ id⊤⊤ (inj₂ tt)
test42 = refl

-- Tasks

⊎comm : (X ⊎ Y) ↔ Y ⊎ X
⊎comm = {!!}

-- × is a commutative monoid with a null element
×ass  : (X × Y) × Z ↔ X × (Y × Z)
×ass = {!!}

×lid  : ⊤ × X ↔ X
×lid = {!!}

×rid  : X × ⊤ ↔ X
×rid = {!!}

×comm : (X × Y) ↔ Y × X
×comm = {!!}

×null : ⊥ × X ↔ ⊥
×null = {!!}

→lid : (⊤ → X) ↔ X
→lid = {!!}

→rnull : (X → ⊤) ↔ ⊤
→rnull = {!!}

→⊥⊤ : (⊥ → X) ↔ ⊤
→⊥⊤ = {!!}

-- distributivity laws
⊎×dist : (X ⊎ Y) × Z ↔ (X × Z) ⊎ (Y × Z)
⊎×dist = {!!}

→×dist : X → (Y × Z) ↔ (X → Y) × (X → Z)
→×dist = {!!}

-- Szorgalmi:
--×⊎dist : (X × Y) ⊎ Z ↔ (X ⊎ Z) × (Y ⊎ Z) -- this is not an isomorphism
--⊎→dist : (X ⊎ Y) → Z ↔ (X → Z) × (Y → Z)
--×→dist : (X × Y) → Z ↔ X → (Y → Z)

---------------------------------------------------------
-- Logic
---------------------------------------------------------

-- negation

anything : ¬ X → X → Y
anything = {!!}
-- ¬¬ is a monad

¬¬return : X → ¬ ¬ X
¬¬return = {!!}

¬¬¬return : ¬ X → ¬ ¬ ¬ X
¬¬¬return = {!!}

¬¬join : ¬ ¬ ¬ ¬ X → ¬ ¬ X
¬¬join = {!!}

¬⊎ : ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
¬⊎ = {!!}
    
¬× : ¬ (X × Y) ← ¬ X ⊎ ¬ Y
¬× = {!!}

build→ : ¬ X ⊎ Y → (X → Y)
build→ = {!!}

¬¬invol : ¬ ¬ ¬ X ↔ ¬ X
¬¬invol = {!!}

nocontra : ¬ (X ↔ ¬ X)
nocontra = {!!}

¬¬dnp : ¬ ¬ (¬ ¬ X → X)
¬¬dnp = {!!}
