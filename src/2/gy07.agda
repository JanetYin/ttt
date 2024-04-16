module gy07 where

open import Lib.Sigma
open import Lib.Sum
open import Lib.Bool
open import Lib.Equality
open import Lib.Empty
open import Lib.Nat
open import Lib.Dec
open import Lib.Dec.PatternSynonym
open import Lib.Function using (_$_)

------------------------------------------------------
-- statements as parameters
------------------------------------------------------

blowUp : ((A : Set) → ¬ A) → ⊥
blowUp f = f ⊤ tt
-- what's the difference with this?
-- example : (A : Set) → ¬ A → ⊥
-- example A x = {!   !}

-- something like this may appear in the exam

---------------------------------------------------------
-- predicate (first order) logic example
---------------------------------------------------------

notExists↔noneOf : ∀{i}{A : Set i} → (P : A → Set) →
                        (∀ x → ¬ (P x)) ↔ ¬ (Σ A (λ x → P x))
fst (notExists↔noneOf P) f x = f (fst x) (snd x)
snd (notExists↔noneOf P) f a pa = f (a , pa)

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
  ONE = Σ Person λ p → Σ Person λ c → c childOf p × (∀ (y : Person) → ¬ (y childOf p) ⊎ y sameAs c)

  -- Define the relation _parentOf_.
  _parentOf_ : Person → Person → Set
  x parentOf y = y childOf x

  -- Formalise: No one is the parent of everyone.
  NOPE : Set
  NOPE = ¬ Σ Person λ p → ∀ (x : Person) → p parentOf x

  NOPE' : Set
  NOPE' = ∀ (p : Person) → ¬ (∀ (x : Person) → p parentOf x)

  -- Prove that if Ann has no children then Kate is not the child of Ann.
  AK : ¬ (Σ Person λ y → y childOf Ann) → ¬ (Kate childOf Ann)
  AK f kca = f (Kate , kca)

  -- Prove that if there is no person who is his own parent than no one is the parent of everyone.
  ¬xpopxthenNOPE : ¬ (Σ Person λ x → x parentOf x) → NOPE
  ¬xpopxthenNOPE f (p , g) = f (p , g p)

---------------------------------------------------------
-- predicate (first order) logic laws
---------------------------------------------------------


∀×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
fst (∀×-distr A P Q) x = (λ a → fst (x a)) , λ a → snd (x a )
snd (∀×-distr A P Q) x a = (fst x a) , (snd x a)

∀⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a) ⊎ ((a : A) → Q a) → ((a : A) → P a ⊎ Q a)
∀⊎-distr A P Q (yes r) a = yes (r a)
∀⊎-distr A P Q (no l) a = no (l a)
-- ez miért csak odafelé megy?
-- miért nem ↔ van közte?

Σ×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a × Q a)  → Σ A P × Σ A Q
Σ×-distr A P Q (fs , sn) = (fs , fst sn) , (fs , snd sn)

Σ⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a)  ↔ Σ A P ⊎ Σ A Q
fst (Σ⊎-distr A P Q) (fs , sn) = case sn (λ x → yes (fs , x)) λ x → no (fs , x)
snd (Σ⊎-distr A P Q) x = case x (λ s → (fst s) , yes (snd s)) (λ s → (fst s) , (no (snd s)))

¬∀        :    (A : Set)(P : A → Set)              → (Σ A λ a → ¬ P a)      → ¬ ((a : A) → P a)
¬∀ A P (fs , sn) x = sn (x fs)

-- Ugyanez van a fájl tetején is:
¬Σ        :    (A : Set)(P : A → Set)              → (¬ Σ A λ a → P a)      ↔ ((a : A) → ¬ P a)
fst (¬Σ A P) x a x₁ = x (a , x₁)
snd (¬Σ A P) x (fs , sn) = x fs sn

¬¬∀-nat   :    (A : Set)(P : A → Set)              → ¬ ¬ ((x : A) → P x)    → (x : A) → ¬ ¬ (P x)
¬¬∀-nat A P x x₁ x₂ = x λ x₃ → x₂ (x₃ x₁)

∀⊎-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (((a : A) → P a ⊎ Q a) → ((a : A) → P a) ⊎ ((a : A) → Q a)))
∀⊎-distr' x = case (x Bool (λ b → if b then ⊥ else ⊤) (if_then ⊤ else ⊥) λ where false → inl tt
                                                                                 true → inr tt) (λ x₁ → x₁ true) ( _$ false) -- for the brave and for the pain

Σ×-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (Σ A P × Σ A Q → Σ A λ a → P a × Q a))
Σ×-distr' w = let g = w Bool (λ x → if x then ⊥ else ⊤) (λ x → if x then ⊤ else ⊥) ((false , tt) , true , tt) in h g where
  h : Σ Bool (λ a → (if a then ⊥ else ⊤) × (if a then ⊤ else ⊥)) → ⊥
  h (false , sn) = snd sn
  h (true , sn) = fst sn
 
Σ∀       : (A B : Set)(R : A → B → Set)        → (Σ A λ x → ∀ (y : B) → R x y) → ∀ (y : B) → Σ A λ x → R x y
Σ∀ A B R x y = fst x , snd x y
AC       : (A B : Set)(R : A → B → Set)        → (∀ (x : A) → Σ B λ y → R x y) → Σ (A → B) λ f → ∀ (x : A) → R x (f x)
AC A B R x = (λ a → fst (x a)) , λ a → snd (x a)
 