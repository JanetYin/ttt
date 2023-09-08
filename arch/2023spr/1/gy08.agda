open import lib

---------------------------------------------------------
-- higher order logic
------------------------------------------------------

Dec : ∀{i} → Set i → Set i
Dec A = A ⊎ ¬ A

f4 : Dec ((X Y : Set) → X ⊎ Y → Y)
f4 = inr λ f → f ⊤ ⊥ (inl tt)

-- X = i      X = h
-- Y = h VAGY Y = i
-- Z = h      Z = h
f5 : Dec ((X Y Z : Set) → (X → Z) ⊎ (Y → Z) → (X ⊎ Y → Z))
f5 = inr λ f → f ⊥ ⊤ ⊥ (inl (λ b → b)) (inr tt)

f6 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f6 = inl λ _ _ _ → λ (f , g) (x , y) → g y

-- X = h
-- Y = i
-- Z = h
f7 : Dec ((X Y Z : Set) → (X × Y → Z) → (X → Z) × (Y → Z))
f7 = inr λ f → snd (f ⊥ ⊤ ⊥ fst) tt

f8 : Dec ((X Y Z : Set) → (X ⊎ Y × Z) → (X ⊎ Y) × (X ⊎ Z))
f8 = inl λ where X Y Z (inl x) → inl x , inl x
                 X Y Z (inr (y , z)) → inr y , inr z

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
  -- ∃y (y childOf x)
  _hasChild : Person → Set
  x hasChild = Σ Person λ y → y childOf x

  -- Formalise: Ann is not a child of Kate.
  ANK : Set
  ANK = ¬ (Ann childOf Kate)

  -- Formalise: there is someone with exactly one child.
  ONE : Set
  ONE = Σ Person (λ p → (Σ Person λ x → x childOf p × ((y : Person) → y childOf p → x sameAs y)))

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
Σ×-distr A P Q (a , pa , qa) = (a , pa) , a , qa
Σ⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a)  ↔ Σ A P ⊎ Σ A Q
Σ⊎-distr A P Q = to , from where
  to : (Σ A λ a → P a ⊎ Q a) → Σ A P ⊎ Σ A Q
  to (a , inl pa) = inl (a , pa)
  to (a , inr qa) = inr (a , qa)

  from : Σ A P ⊎ Σ A Q → (Σ A λ a → P a ⊎ Q a)
  from (inl (a , pa)) = a , inl pa
  from (inr (a , qa)) = a , inr qa

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


P : ℕ → Set
P zero = ⊤
P (suc n) = ⊥

Q : ℕ → Set
Q zero = ⊥
Q (suc n) = ⊤

Σ×-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (Σ A P × Σ A Q → Σ A λ a → P a × Q a))
Σ×-distr' w with w ℕ P Q ((0 , tt) , (1 , tt))
... | zero , paqa = snd paqa
... | suc n , paqa = fst paqa

indℕ : (n : ℕ)(P : ℕ → Set) → P 0 → ((k : ℕ) → P k → P (suc k)) → P n
indℕ zero P p0 f = p0
indℕ (suc n) P p0 f = f n (indℕ n P p0 f)
 
Σ∀       : (A B : Set)(R : A → B → Set)        → (Σ A λ x → (y : B) → R x y) → (y : B) → Σ A λ x → R x y
Σ∀ = {!!}
AC       : (A B : Set)(R : A → B → Set)        → ((x : A) → Σ B λ y → R x y) → Σ (A → B) λ f → (x : A) → R x (f x)
AC = {!!}
