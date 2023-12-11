open import Lib
open import Lib.Dec.PatternSynonym

------------------------------------------------------
-- statements as parameters
------------------------------------------------------

blowUp : ((A : Set) -> ¬ A) -> ⊥
blowUp f = f ⊤ tt
-- what's the difference with this?
-- (A : Set) -> (¬ A -> ⊥)

-- something like this may appear in the exam

------------------------------------------------------
-- practicing
------------------------------------------------------

f4 : Dec ((X Y : Set) → X ⊎ Y → Y)
f4 = inr λ f -> f ⊤ ⊥ (inl tt)

f5 : Dec ((X Y Z : Set) → (X → Z) ⊎ (Y → Z) → (X ⊎ Y → Z))
f5 = inr λ f -> f ⊥ ⊤ ⊥ (inl (λ b -> b)) (inr tt)

f6 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f6 = inl λ {_ _ _ (xtoz , ytoz) (x , y) -> xtoz x}

f7 : Dec ((X Y Z : Set) → (X × Y → Z) → (X → Z) × (Y → Z))
f7 = inr λ f -> fst (f ⊤ ⊥ ⊥ snd) tt

f8 : Dec ((X Y Z : Set) → (X ⊎ Y × Z) → (X ⊎ Y) × (X ⊎ Z))
f8 = inl λ _ _ _ xvyaz -> case xvyaz (λ x -> inl x , inl x)
                                      λ {(y , z) -> inr y , inr z}

f9 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → (X ⊎ Y × Z))
f9 = inl λ {_ _ _ (xvy , xvz) -> case xvy (λ x -> inl x)
                                          (λ y -> case xvz (λ x -> inl x)
                                                           (λ z -> inr (y , z)))}

f10 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → ((X ⊎ Y) × Z))
f10 = inr λ f -> snd (f ⊤ ⊤ ⊥ (inl tt , inl tt))

-- ezt nem lehet sem bizonyítani, sem cáfolni
f+ : Dec ((X Y Z : Set) → (X × Y → Z) → (X → Z) ⊎ (Y → Z))
f+ = inr λ f -> case (f {!!} {!!} ⊥ {!!}) {!!} {!!}

---------------------------------------------------------
-- predicate (first order) logic example
---------------------------------------------------------

-- függő típusokkal tudunk igazán értelmes logikát csinálni
-- ez az elsőrendű logika

-- Σ X (λ x -> P x)
-- létezik olyan X típusú dolog (hívjuk x-nek), amire a P igaz
-- ∀ (x : X) -> P x        (ez kvázi (x : X) -> P x-szel ekvivalens, de a ": X"- ilyenkor elhagyható)
-- minden X típusú dologra a P igaz


-- erre mindjárt visszatérünk
notExists↔noneOf : ∀{i}{A : Set i} -> (P : A -> Set) ->
                        (∀ x -> ¬ (P x)) ↔ ¬ (Σ A (λ x -> P x))
notExists↔noneOf = {!!}

module People
  (Person    : Set)
  (Ann       : Person)
  (Kate      : Person)
  (Peter     : Person)
  (_childOf_ : Person → Person → Set)
  (_sameAs_  : Person → Person → Set) -- ez most itt az emberek egyenlosege
  where

  -----------
  -- Statements
  -----------

  -- Define the _hasChild predicate.
  _hasChild : Person → Set
  x hasChild = {!!}

  -- Formalise: Ann is not a child of Kate.
  ANK : Set
  ANK = {!!}

  -- Formalise: there is someone with exactly one child.
  ONE : Set
  ONE = {!!}

  -- Define the relation _parentOf_.
  _parentOf_ : Person → Person → Set
  x parentOf y = {!!}

  -- Formalise: No one is the parent of everyone.
  NOPE : Set
  NOPE = ¬ Σ Person (λ poe -> ∀ (c : Person) -> poe parentOf c)
  -- NOPE = ∀ (p : Person) -> ¬ (∀ (c : Person) -> p parentOf c)

  -----------
  -- Proofs
  -----------

  -- Prove that if Ann has no children then Kate is not the child of Ann.
  AK : ¬ (Σ Person λ y → y childOf Ann) → ¬ (Kate childOf Ann)
  AK f kca = f (Kate , kca)

  -- Prove that if there is no person who is his own parent than no one is the parent of everyone.
  ¬xpopxthenNOPE : ¬ (Σ Person λ x → x parentOf x) → NOPE
  ¬xpopxthenNOPE nxpx (p , ppOfE) = nxpx (p , ppOfE p)

---------------------------------------------------------
-- predicate (first order) logic laws
---------------------------------------------------------

∀×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
fst (∀×-distr A P Q) f = (λ a -> fst (f a)) , λ a -> snd (f a)
snd (∀×-distr A P Q) (f , g) a = f a , g a
∀⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a) ⊎ ((a : A) → Q a) ↔ ((a : A) → P a ⊎ Q a)
∀⊎-distr = {!!}
-- ez miért csak odafelé? gondold meg
Σ×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a × Q a)  → Σ A P × Σ A Q
Σ×-distr A P Q (a , pa , qa) = (a , pa) , a , qa
Σ⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a)  ↔ Σ A P ⊎ Σ A Q
Σ⊎-distr = {!!}
-- fordítva ez sem (az viszont nem is hamis)
¬∀ : (A : Set)(P : A → Set) → (Σ A λ a → ¬ P a)
                             → ¬ ((a : A) → P a)
¬∀ A P (a , npa) f = npa (f a)
⊎↔ΣBool   :    (A B : Set)                         → (A ⊎ B)                ↔ Σ Bool (λ b → if b then A else B)
⊎↔ΣBool = {!!}
¬¬∀-nat   :    (A : Set)(P : A → Set)              → ¬ ¬ ((x : A) → P x)    → (x : A) → ¬ ¬ (P x)
¬¬∀-nat = {!!}

Σ×-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (Σ A P × Σ A Q → Σ A λ a → P a × Q a))
Σ×-distr' w = {!!}
 
Σ∀       : (A B : Set)(R : A → B → Set)        → (Σ A λ x → (y : B) → R x y) → (y : B) → Σ A λ x → R x y
Σ∀ = {!!}
AC       : (A B : Set)(R : A → B → Set)        → ((x : A) → Σ B λ y → R x y) → Σ (A → B) λ f → (x : A) → R x (f x)
AC = {!!}
