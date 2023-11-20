open import Lib
open import Lib.Dec.PatternSynonym

---------------------------------------------------------
-- higher order logic
------------------------------------------------------

{-
| matematika |    logika    |   agda |
|   1 - 0    | true - false | ⊤ - ⊥ |
|     +      |   v (vagy)   |   ⊎    |
|     *      |   ^ (és)     |   ×    |
| ^ (hatvány)|      ⊃       |   →    |
| (1 -_)     |      ¬       |  _→ ⊥ |


-}

f4 : Dec ((X Y : Set) → X ⊎ Y → Y)
f4 = no λ x → x ⊤ ⊥ (inl tt)

f5 : Dec ((X Y Z : Set) → (X → Z) ⊎ (Y → Z) → (X ⊎ Y → Z))
f5 = no λ x → x ⊤ ⊥ ⊥ (no (λ h → h)) (yes tt)

f6 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f6 = yes (λ where X Y Z (fs , sn) (f , s) → sn s)

demorgen : {A B : Set } → ¬ ¬ (¬ (A × B) → ¬ A ⊎ ¬ B) -- Konstruktív logikában vagyunk, így a dupla tagadás (¬ (¬ (A × B) → ¬ A ⊎ ¬ B)) itt nem működne. Azért, hogy ezt kiküszöböljük, még ráteszünk tagadást, amit így már tudunk bizonyítani.
demorgen f = f 
  λ x → yes         -- Menjünk el az egyik irányba!
    (λ a → f        -- Sajnos még csak egy "A"-m van, honnan szerzek "B"-t? Mi lenne, ha elmennénk a másik irányba? Próbáljuk ki!
    (λ _ → no       -- Mivel újra meghívtam f-et, így el tudtam menni a másik irányba! Ezt logikában "időutazásnak" hívják, mivel egy előző hibát (információ vesztést) kijavítunk azzal, hogy visszatérünk oda, ahol hibáztunk (információt vesztettünk)
      (λ b → x (a , b)))) -- Itt már meg tudom hívni "x"-et, mivel van "A" típusú értékem is, és "B" típusú értékem is.

f7 : Dec ((X Y Z : Set) → (X × Y → Z) → (X → Z) × (Y → Z))
f7 = {!!}

f8 : Dec ((X Y Z : Set) → (X ⊎ Y × Z) → (X ⊎ Y) × (X ⊎ Z))
f8 = yes λ _ _ _ x → case x inl (λ where (s , _) → inr s) , case x inl λ where (f , s) → inr s

f9 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → (X ⊎ Y × Z))
f9 = {!!}

f10 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → ((X ⊎ Y) × Z))
f10 = {!!}

---------------------------------------------------------
-- predicate (first order) logic example
---------------------------------------------------------

module People
  (Person    : Set)
  (Ann       : Person)
  (Kate      : Person)
  (Peter     : Person)
  (_childOf_ : Person → Person → Set)
  (_sameAs_  : Person → Person → Set) -- ez most itt az emberek egyenlosege
  where

  -- Define the _hasChild predicate.
  _hasChild : Person → Set
  x hasChild = Σ Person λ p → p childOf x

  -- Formalise: Ann is not a child of Kate.
  ANK : Set
  ANK = ¬ (Ann childOf Kate)

  -- Formalise: there is someone with exactly one child.
  ONE : Set
  ONE = Σ Person λ p → Σ Person λ x → Σ Person λ y → x childOf p × y childOf p → x sameAs y

  -- Define the relation _parentOf_.
  _parentOf_ : Person → Person → Set
  x parentOf y = {!!}

  -- Formalise: No one is the parent of everyone.
  NOPE : Set
  NOPE = {!!}

  -- Prove that if Ann has no children then Kate is not the child of Ann.
  AK : ¬ (Σ Person λ y → y childOf Ann) → ¬ (Kate childOf Ann)
  AK = {!!}

  -- Prove that if there is no person who is his own parent than no one is the parent of everyone.
  ¬NOPE : ¬ (Σ Person λ x → x parentOf x) → NOPE
  ¬NOPE = {!!}

---------------------------------------------------------
-- predicate (first order) logic laws
---------------------------------------------------------

∀×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
∀×-distr = {!!}
∀⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a) ⊎ ((a : A) → Q a) → ((a : A) → P a ⊎ Q a)
∀⊎-distr = {!!}
Σ×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a × Q a)  → Σ A P × Σ A Q
Σ×-distr = {!!}
Σ⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a)  ↔ Σ A P ⊎ Σ A Q
Σ⊎-distr = {!!}
¬∀        :    (A : Set)(P : A → Set)              → (Σ A λ a → ¬ P a)      → ¬ ((a : A) → P a)
¬∀ = {!!}
¬Σ        :    (A : Set)(P : A → Set)              → (¬ Σ A λ a → P a)      ↔ ((a : A) → ¬ P a)
¬Σ = {!!}
⊎↔ΣBool   :    (A B : Set)                         → (A ⊎ B)                ↔ Σ Bool (λ b → if b then A else B)
⊎↔ΣBool = {!!}
¬¬∀-nat   :    (A : Set)(P : A → Set)              → ¬ ¬ ((x : A) → P x)    → (x : A) → ¬ ¬ (P x)
¬¬∀-nat = {!!}

∀⊎-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (((a : A) → P a ⊎ Q a) → ((a : A) → P a) ⊎ ((a : A) → Q a)))
∀⊎-distr' = {!!}

Σ×-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (Σ A P × Σ A Q → Σ A λ a → P a × Q a))
Σ×-distr' w = {!!}
 
Σ∀       : (A B : Set)(R : A → B → Set)        → (Σ A λ x → (y : B) → R x y) → (y : B) → Σ A λ x → R x y
Σ∀ = {!!}
AC       : (A B : Set)(R : A → B → Set)        → ((x : A) → Σ B λ y → R x y) → Σ (A → B) λ f → (x : A) → R x (f x)
AC = {!!}
 