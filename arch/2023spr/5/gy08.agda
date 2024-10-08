open import lib

---------------------------------------------------------
-- higher order logic
------------------------------------------------------

Dec : ∀{i} → Set i → Set i
Dec A = A ⊎ ¬ A

f4 : Dec ((X Y : Set) → X ⊎ Y → Y)
f4 = inr λ f → f ⊤ ⊥ (inl tt)

f5 : Dec ((X Y Z : Set) → (X → Z) ⊎ (Y → Z) → (X ⊎ Y → Z))
f5 = inr λ f → f ⊤ ⊥ ⊥ (inr (λ x → x)) (inl tt)

f6 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f6 = inl λ where X Y Z (fst₁ , snd₁) (fst₂ , snd₂) → fst₁ fst₂

f7 : Dec ((X Y Z : Set) → (X × Y → Z) → (X → Z) × (Y → Z))
f7 = inr λ x → fst (x ⊤ ⊥ ⊥ snd) tt

f8 : Dec ((X Y Z : Set) → (X ⊎ Y × Z) → (X ⊎ Y) × (X ⊎ Z))
f8 = inl λ where X Y Z (inl x) → inl x , inl x
                 X Y Z (inr (y , z)) → inr y , inr z

f9 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → (X ⊎ Y × Z))
f9 = inl λ where X Y Z (inl x , _) → inl x
                 X Y Z (inr _ , inl x) → inl x
                 X Y Z (inr y , inr z) → inr (y , z)

f10 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → ((X ⊎ Y) × Z))
f10 = inr λ x → snd (x ⊤ (Bool × ℕ ⊎ ⊤) ⊥ (inl tt , inl tt))

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
  -- ONE = Σ Person λ p → (a : Person) → (b : Person) → a childOf p × b childOf p → a sameAs b
  ONE = Σ Person λ p → Σ Person λ c → c childOf p × ((person : Person) → person childOf p → person sameAs c)

  -- Define the relation _parentOf_.
  _parentOf_ : Person → Person → Set
  x parentOf y = y childOf x

  -- Formalise: No one is the parent of everyone.
  NOPE : Set
  -- NOPE = (p : Person) → Σ Person λ c → ¬ (c childOf p)
  NOPE = ¬ (Σ Person λ p → (x : Person) → p parentOf x)

  -- Prove that if Ann has no children then Kate is not the child of Ann.
  AK : ¬ (Σ Person λ y → y childOf Ann) → ¬ (Kate childOf Ann)
  AK = λ x kca → x (Kate , kca)

  -- Prove that if there is no person who is his own parent than no one is the parent of everyone.
  ¬NOPE : ¬ (Σ Person λ x → x parentOf x) → NOPE
  ¬NOPE x (s1 , s2) = x (s1 , s2 s1)

---------------------------------------------------------
-- predicate (first order) logic laws
---------------------------------------------------------

∀×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
∀×-distr = λ A P Q → (λ x → (λ a → fst (x a)) , λ a → snd (x a)) , λ (pa , qa) a → pa a , qa a

∀⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a) ⊎ ((a : A) → Q a) → ((a : A) → P a ⊎ Q a)
∀⊎-distr = λ where A P Q (inl x) a → inl (x a)
                   A P Q (inr x) a → inr (x a)

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
