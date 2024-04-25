module gy07 where

open import Lib
open import Lib.Dec.PatternSynonym

------------------------------------------------------
-- statements as parameters
------------------------------------------------------

blowUp : ((A : Set) -> ¬ A) -> ⊥
blowUp f = f ⊤ tt
-- what's the difference with this?
-- (A : Set) -> ¬ A -> ⊥

-- something like this may appear in the exam

------------------------------------------------------
-- practicing
------------------------------------------------------

f4 : Dec ((X Y : Set) → X ⊎ Y → Y)
f4 = {!!}

f5 : Dec ((X Y Z : Set) → (X → Z) ⊎ (Y → Z) → (X ⊎ Y → Z))
f5 = {!!}

f6 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f6 = {!!}

f7 : Dec ((X Y Z : Set) → (X × Y → Z) → (X → Z) × (Y → Z))
f7 = {!!}

f8 : Dec ((X Y Z : Set) → (X ⊎ Y × Z) → (X ⊎ Y) × (X ⊎ Z))
f8 = {!!}

f9 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → (X ⊎ Y × Z))
f9 = {!!}

f10 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → ((X ⊎ Y) × Z))
f10 = {!!}

---------------------------------------------------------
-- predicate (first order) logic example
---------------------------------------------------------

-- erre mindjárt visszatérünk
notExists↔noneOf : ∀{i}{A : Set i} -> (P : A -> Set) ->
                        (∀ x -> ¬ (P x)) ↔ ¬ (Σ A (λ x -> P x))
fst (notExists↔noneOf P) x (fs , sn) = x fs sn
snd (notExists↔noneOf P) ¬s a p = ¬s (a , p)

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
  x hasChild = Σ Person (λ y → y childOf x)

  -- Formalise: Ann is not a child of Kate.
  ANK : Set
  ANK = ¬ (Ann childOf Kate)

  -- Formalise: there is someone with exactly one child.
  ONE : Set
  ONE = Σ Person (λ x → Σ Person (λ y → y childOf x × (∀ (z : Person) → z childOf x → z sameAs y)))

  -- Define the relation _parentOf_.
  _parentOf_ : Person → Person → Set
  x parentOf y = y childOf x

  -- Formalise: No one is the parent of everyone.
  NOPE : Set
  NOPE = ¬ Σ Person (λ x → ∀ (z : Person) → z childOf x)

  -- Prove that if Ann has no children then Kate is not the child of Ann.
  AK : ¬ (Σ Person λ y → y childOf Ann) → ¬ (Kate childOf Ann)
  AK = {!!}

  -- Prove that if there is no person who is his own parent than no one is the parent of everyone.
  ¬xpopxthenNOPE : ¬ (Σ Person λ x → x parentOf x) → NOPE
  ¬xpopxthenNOPE = {!!}

---------------------------------------------------------
-- predicate (first order) logic laws
---------------------------------------------------------

∀×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
fst (∀×-distr A P Q) x = (λ a → fst (x a)) , λ a → snd (x a)
snd (∀×-distr A P Q) x a = (fst x a) , (snd x a)

∀⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a) ⊎ ((a : A) → Q a) → ((a : A) → P a ⊎ Q a)
∀⊎-distr A P Q x a = case x (λ f → yes (f a)) λ f → no (f a)
-- ez miért csak odafelé?
Σ×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a × Q a)  → Σ A P × Σ A Q
Σ×-distr A P Q x = ((fst x) , fst (snd x)) , fst x , snd (snd x)
Σ⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a)  ↔ Σ A P ⊎ Σ A Q
fst (Σ⊎-distr A P Q) x = case (snd x) (λ p → yes ((fst x) , p)) λ q → no ((fst x) , q)
snd (Σ⊎-distr A P Q) x = case x (λ p → (fst p) , yes (snd p)) λ q → (fst q) , (no (snd q))
¬∀        :    (A : Set)(P : A → Set)              → (Σ A λ a → ¬ P a)      → ¬ ((a : A) → P a)
¬∀ A P x u = snd x (u (fst x))
¬Σ        :    (A : Set)(P : A → Set)              → (¬ Σ A λ a → P a)      ↔ ((a : A) → ¬ P a)
fst (¬Σ A P) x a p = x (a , p)
snd (¬Σ A P) u s = u (fst s) (snd s)
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
AC A B R x = (λ a → fst (x a)) , λ a → snd (x a)
