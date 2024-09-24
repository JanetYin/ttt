module gy08 where

open import Lib
-- open import Lib.Dec.PatternSynonym

------------------------------------------------------
-- statements as parameters
------------------------------------------------------

blowUp : ((A : Set) → ¬ A) → ⊥
blowUp f = f ⊤ tt
-- what's the difference with this?
-- (A : Set) → ¬ A → ⊥

-- something like this may appear in the exam

---------------------------------------------------------
-- predicate (first order) logic example
---------------------------------------------------------

notExists↔noneOf : ∀{i}{A : Set i} → (P : A → Set) →
                        ¬ (Σ A (λ x → P x)) ↔ (∀ x → ¬ (P x))
fst (notExists↔noneOf P) x x₁ x₂ = x (x₁ , x₂)
snd (notExists↔noneOf P) x x₁ = x (fst x₁) (snd x₁)

module People
  (Person    : Set) -- Univerzum
  (Ann       : Person)
  (Kate      : Person)
  (Peter     : Person)
  (_childOf_ : Person → Person → Set)
  (_sameAs_  : Person → Person → Set) -- ez most itt az emberek egyenlosege
  -- reláció
  where

  -- Define the _hasChild predicate.
  _hasChild : Person → Set -- \GS
  x hasChild = Σ Person λ p → p childOf x -- ∃ p : Person, p childOf x

  -- Formalise: Ann is not a child of Kate.
  ANK : Set
  ANK = ¬ (Ann childOf Kate)

  -- Formalise: there is someone with exactly one child.
  ONE : Set
  ONE = Σ Person λ p → p hasChild × ((k : Person) → (l : Person) → k childOf p × l childOf p → l sameAs k)

  -- Define the relation _parentOf_.
  _parentOf_ : Person → Person → Set
  x parentOf y = y childOf x

  -- Minden emberre igaz, hogy nem a saját gyereke
  notOwnChild : Set
  notOwnChild = (p : Person) → ¬ (p childOf p)

  -- Formalise: No one is the parent of everyone.
  NOPE : Set
  NOPE = Person

  -- Prove that if Ann has no children then Kate is not the child of Ann.
  AK : ¬ (Σ Person λ y → y childOf Ann) → ¬ (Kate childOf Ann)
  AK = {!!}

  -- Prove that if there is no person who is his own parent than no one is the parent of everyone.
  ¬xpopxthenNOPE : ¬ (Σ Person λ x → x parentOf x) → NOPE
  ¬xpopxthenNOPE = λ _ → Peter

---------------------------------------------------------
-- predicate (first order) logic laws
---------------------------------------------------------

∀×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a × Q a) ↔ ((a : A) → P a) × ((a : A) → Q a)
fst (fst (∀×-distr A P Q) x) a = fst (x a)
snd (fst (∀×-distr A P Q) x) a = snd (x a)
fst (snd (∀×-distr A P Q) x a) = fst x a
snd (snd (∀×-distr A P Q) x a) = snd x a

-- !!!
Σ⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a) ↔ Σ A P ⊎ Σ A Q
fst (Σ⊎-distr A P Q) (a , inl Pa) = inl (a , Pa)
fst (Σ⊎-distr A P Q) (a , inr Qa) = inr (a , Qa)
snd (Σ⊎-distr A P Q) (inl (a , Pa)) = a , inl Pa
snd (Σ⊎-distr A P Q) (inr (a , Qa)) = a , inr Qa

-- !!!
∀⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a) ⊎ ((a : A) → Q a) → ((a : A) → P a ⊎ Q a)
∀⊎-distr A P Q (inl a→Pa) a = inl (a→Pa a)
∀⊎-distr A P Q (inr a→Qa) a = inr (a→Qa a)
-- ez miért csak odafelé megy?
-- miért nem ↔ van közte?

-- !!!
∀⊎-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (((a : A) → P a ⊎ Q a) → ((a : A) → P a) ⊎ ((a : A) → Q a)))
∀⊎-distr' x with x Bool P Q (λ { false → inl tt ; true → inr tt })
  where
    P Q : Bool → Set
    P false = ⊤
    P true = ⊥
    Q false = ⊥
    Q true = ⊤
... | inl a = a true
... | inr b = b false

-- !!!
Σ×-distr  : Dec ((A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a × Q a)  → Σ A P × Σ A Q)
Σ×-distr = inl (λ { A P Q (a , Pa , Qa) → (a , Pa) , (a , Qa) })

-- !!!
Σ×-distr' : Dec ((A : Set)(P : A → Set)(Q : A → Set) → (Σ A P × Σ A Q → Σ A λ a → P a × Q a))
Σ×-distr' = inr helper
  where
    P Q : Bool → Set
    P false = ⊤
    P true = ⊥
    Q false = ⊥
    Q true = ⊤
    helper : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (Σ A P × Σ A Q → Σ A λ a → P a × Q a))
    helper x with x Bool P Q ((false , tt) , true , tt)
    ... | false , Pa , Qa = Qa
    ... | true , Pa , Qa = Pa

¬∀        :    (A : Set)(P : A → Set)              → (Σ A λ a → ¬ P a)      → ¬ ((a : A) → P a)
¬∀ A P x x₁ = snd x (x₁ (fst x))

-- Ugyanez van a fájl tetején is:
¬Σ        :    (A : Set)(P : A → Set)              → (¬ Σ A λ a → P a)      ↔ ((a : A) → ¬ P a)
fst (¬Σ A P) x a x₁ = x (a , x₁)
snd (¬Σ A P) x x₁ = x (fst x₁) (snd x₁)

¬¬∀-nat   :    (A : Set)(P : A → Set)              → ¬ ¬ ((x : A) → P x)    → (x : A) → ¬ ¬ (P x)
¬¬∀-nat A P x x₁ x₂ = x (λ x₃ → x₂ (x₃ x₁))
 
Σ∀       : (A B : Set)(R : A → B → Set)        → (Σ A λ x → (y : B) → R x y) → (y : B) → Σ A λ x → R x y
Σ∀ A B R x y = (fst x) , (snd x y)

AC       : (A B : Set)(R : A → B → Set)        → ((x : A) → Σ B λ y → R x y) → Σ (A → B) λ f → (x : A) → R x (f x)
AC A B R x = (λ x₁ → fst (x x₁)) , λ x₁ → snd (x x₁)

P04 : (A : Set)(P : A → Set) → ((x : A) → ¬ P x) → {!   !} -- (¬ Σ A λ a → P a)   
P04 = {!   !}