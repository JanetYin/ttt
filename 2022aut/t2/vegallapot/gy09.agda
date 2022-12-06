open import lib

---------------------------------------------------------
--# homework: zero-order logic
------------------------------------------------------

Dec : ∀{i} → Set i → Set i
Dec A = A ⊎ ¬ A

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

module People
  --these are like postulates
  (Person    : Set)
  (Ann       : Person)
  (Kate      : Person)
  (Peter     : Person)
  (_childOf_ : Person → Person → Set)
  (_sameAs_  : Person → Person → Set) -- ez most itt az emberek egyenlosege
  where

  -- Define the _hasChild predicate.
  -- ∃ y : y childOf x
  _hasChild : Person → Set
  x hasChild = Σ Person (λ p → p childOf x)

  everyoneIsChildOf_ : Person → Set
  everyoneIsChildOf x = (p : Person) → p childOf x 

--#NOTE: learn until here

  -- Formalise: Ann is not a child of Kate.
  ANK : Set
  ANK = ¬ (Ann childOf Kate)

  -- Formalise: there is someone with exactly one child.
  ONE : Set
  ONE = Σ Person λ x → Σ Person λ y → y childOf x × (∀ (othery : Person) → (othery childOf x → othery sameAs y))

  -- Define the relation _parentOf_.
  _parentOf_ : Person → Person → Set
  x parentOf y = y childOf x

  -- Formalise: No one is the parent of everyone.
  NOPE NOPE' NOPE'' : Set
  NOPE = ¬ (Σ Person λ x → everyoneIsChildOf x)
  NOPE' = ∀ (x : Person) → ¬ (∀ (p : Person) → p childOf x )
  NOPE'' = ∀ (x : Person) → Σ Person (λ p → ¬ (p childOf x))

  -- Prove that if Ann has no children then Kate is not the child of Ann.
  AK : ¬ (Σ Person λ y → y childOf Ann) → ¬ (Kate childOf Ann)
  AK = λ nca → λ kca → nca (Kate , kca)

  -- Prove that if there is no person who is his own parent than no one is the parent of everyone.
  ¬NOPE : ¬ (Σ Person λ x → x parentOf x) → NOPE
  ¬NOPE = λ npx → λ (gf , apgf) → npx (gf , apgf gf)

---------------------------------------------------------
-- predicate (first order) logic laws
---------------------------------------------------------

--(∀ a : P a ∧ Q a) is equivalent to (∀ a : P a) ∧ (∀ a : Q a)
∀×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
∀×-distr _ P Q = (λ f → (λ a → fst (f a)) , λ a → snd (f a))
               , λ (p , q) a → p a , q a

--this is not true the other way round
∀⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a) ⊎ ((a : A) → Q a) → ((a : A) → P a ⊎ Q a)
∀⊎-distr A P Q = λ { (inl f) → λ a → inl (f a) ;
                      (inr g) → λ a → inr (g a)}

--same with ∃
Σ×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a × Q a)  → Σ A P × Σ A Q
Σ×-distr = {!!}

--this is almost true backwards, but with a restriction
Σ×-distr-back  :    (A : Set)(P : A → Set)(Q : A → Set) → (s : Σ A P × Σ A Q) → (fst (fst s) ≡ fst (snd s)) → (Σ A λ a → P a × Q a)
Σ×-distr-back A P Q s refl = let a = fst (fst s) in
                               a , snd (fst s) , snd (snd s)        --refl is important!

--#NOTE: homework from here
Σ⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a)  ↔ Σ A P ⊎ Σ A Q
Σ⊎-distr = {!!}

--this would need tnd backwards
¬∀        :    (A : Set)(P : A → Set)              → (Σ A λ a → ¬ P a)      → ¬ ((a : A) → P a)
¬∀ = {!!}
¬Σ        :    (A : Set)(P : A → Set)              → (¬ Σ A λ a → P a)      ↔ ((a : A) → ¬ P a)
¬Σ = {!!}
¬¬∀-nat   :    (A : Set)(P : A → Set)              → ¬ ¬ ((x : A) → P x)    → (x : A) → ¬ ¬ (P x)
¬¬∀-nat = {!!}

∀⊎-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (((a : A) → P a ⊎ Q a) → ((a : A) → P a) ⊎ ((a : A) → Q a)))
∀⊎-distr' = {!!}

Σ×-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (Σ A P × Σ A Q → Σ A λ a → P a × Q a))
Σ×-distr' w = {!!}


--if there is a key that opens all doors, then for all doors there is a key that opens it
--(but not the other way round)
Σ∀       : (A B : Set)(R : A → B → Set)        → (Σ A λ x → (y : B) → R x y) → (∀ (y : B) → Σ A (λ x → R x y))
Σ∀ = {!!}

--if for all doors there exists a key that opens it, then there exists a door-key function that for all doors gives a key that opens it (and vice versa)
AC       : (A B : Set)(R : A → B → Set)        → ((x : A) → Σ B λ y → R x y) ↔ (Σ (A → B) (λ f → (x : A) → R x (f x)))
AC A B R = (λ f → (λ a → fst (f a)) , λ a → snd (f a)) ,
           λ s → λ a → (fst s) a , (snd s) a
