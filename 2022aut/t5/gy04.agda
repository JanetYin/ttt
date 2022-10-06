module t5.gy04 where
open import lib

-- List of unicode symbols:
--    →       \to
--            \rightarrow
--    ℕ       \bN           'b'lackboard 'N', there is also \bZ for ℤ, etc
--    λ       \Gl           'G'reek 'l', there is also \GG for Γ, etc
--            \lambda
--    ×       \times
--    ⊎       \u+
--    ⊤       \top
--    ⊥       \bot
--    ↔       \lr
--    ₁       \_1
--    ₐ       \_a
--    ¹       \^1

-- ⊤ and ⊥

-- ⊤ is also called unit

-- ⊤   \top

ex : ⊤
ex = tt

--   _,_

-- ⊤ : type with 1 element
--  _×_ : binary product
--  ⊤   : nullary product

-- from-Bool and to-Bool should be inverses.

--  ⊤ ⊎ ⊤ has two elements:
--    inl tt
--    inr tt

from-Bool : Bool → ⊤ ⊎ ⊤
from-Bool true  = inl tt
from-Bool false = inr tt

to-Bool : ⊤ ⊎ ⊤ → Bool
to-Bool (inl _) = true
to-Bool (inr _) = false

-- A ↔ B = (A → B) × (B → A)
-- A logical equivalence f : A ↔ B consists of functions
--  fst f : A → B, and
--  snd f : B → A

Bool↔⊤⊎⊤ : Bool ↔ ⊤ ⊎ ⊤
Bool↔⊤⊎⊤ = from-Bool , to-Bool

-- ⊥  \bot

-- ⊥ : type with 0 elements
--  _⊎_ : binary sum
--  ⊥   : nullary sum

-- When eliminating A ⊎ B : 2 cases  inl a  and  inr b
-- When eliminating ⊥     : 0 cases

-- It is not possible to create any element of ⊥.

-- elimination:
--   exfalso : {A : Type} → ⊥ → A

exfalso-Bool : ⊥ → Bool
exfalso-Bool x = exfalso x

-- A → B   has  b^a elements

-- ⊤ → ⊥   has  0^1 = 0 elements

-- ⊥ → ⊤   has  1^0 = 1 elements

-- (⊤ → ⊥) ⊎ (⊥ → ⊤) has   0^1 + 1^0 = 1 elements

example-⊥ : (⊤ → ⊥) ⊎ (⊥ → ⊤)
example-⊥ = inr (λ x → exfalso x) -- here x : ⊥

example-⊥' : (⊤ → ⊥) ⊎ (⊥ → ⊤)
example-⊥' = inr (λ x → tt)

example-⊥-test : example-⊥ ≡ example-⊥'; example-⊥-test = refl


-- Algebraic laws

-- (⊎, ⊥) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc⊎₁ : {A B C : Type} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
assoc⊎₁ (inl (inl a)) = inl a
assoc⊎₁ (inl (inr b)) = inr (inl b)
assoc⊎₁ (inr c) = inr (inr c)

assoc⊎₂ : {A B C : Type} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
assoc⊎₂ (inl a) = inl (inl a)
assoc⊎₂ (inr (inl b)) = inl (inr b)
assoc⊎₂ (inr (inr c)) = inr c

assoc⊎ : {A B C : Type} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C)
assoc⊎ = assoc⊎₁ , assoc⊎₂

idl⊎₁ : {A : Type} → ⊥ ⊎ A → A
idl⊎₁ (inl x) = exfalso x
idl⊎₁ (inr x) = x

idl⊎₂ : {A : Type} → A → ⊥ ⊎ A
idl⊎₂ = inr

idl⊎ : {A : Type} → ⊥ ⊎ A ↔ A
idl⊎ = idl⊎₁ , idl⊎₂

-- Corresponds to   n + 0 = n
idr⊎₁ : {A : Type} → A ⊎ ⊥ → A
idr⊎₁ (inl a)  = a
idr⊎₁ (inr e⊥) = exfalso e⊥
-- idr⊎₁ (inr ())
--                 or pattern match on e⊥

idr⊎₂ : {A : Type} → A → A ⊎ ⊥
idr⊎₂ a = inl a

idr⊎ : {A : Type} → A ⊎ ⊥ ↔ A
idr⊎ = idr⊎₁ , idr⊎₂

-- Alternative:
-- idr⊎' : {A : Type} → A ⊎ ⊥ ↔ A
-- idr⊎' .fst = {!!}
-- idr⊎' .snd = {!!}

comm⊎ : {A B : Type} → A ⊎ B ↔ B ⊎ A
comm⊎ = (λ x → case x inr inl) , (λ x → case x inr inl)

-- (×, ⊤) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc× : {A B C : Type} → (A × B) × C ↔ A × (B × C)
assoc× = (λ ((a , b) , c) → (a , (b , c)))
       , (λ p → ((fst p , fst (snd p)) , snd (snd p)))

idl× : {A : Type} → ⊤ × A ↔ A
idl× = snd , (λ a → tt , a)

idr× : {A : Type} → A × ⊤ ↔ A
idr× = fst , (λ a → a , tt)

-- ⊥ is a null element

-- null× : {A : Type} → A × ⊥ ↔ ⊥
-- null× = {!!}

-- distributivity of × and ⊎

dist₁ : {A B C : Type} → A × (B ⊎ C) → (A × B) ⊎ (A × C)
dist₁ (a , inl b) = inl (a , b)
dist₁ (a , inr c) = inr (a , c)

dist₂ : {A B C : Type} → (A × B) ⊎ (A × C) → A × (B ⊎ C)
dist₂ (inl (a , b)) = a , inl b
dist₂ (inr (a , c)) = a , inr c

dist : {A B C : Type} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
dist = dist₁ , dist₂

-- exponentiation laws

curry' : ∀{A B C : Type} → (A × B → C) ↔ (A → B → C)
curry' = (λ f a b → f (a , b))
       , (λ f p → f (fst p) (snd p))

⊎×→ : {A B C D : Type} → ((A ⊎ B) → C) ↔ (A → C) × (B → C)
⊎×→ = (λ f → (λ a → f (inl a)) , (λ b → f (inr b)))
    , (λ (fa , fb) aorb → case aorb fa fb)

law^0 : {A : Type} → (⊥ → A) ↔ ⊤
law^0 = (λ _ → tt) , (λ _ → exfalso)

law^1 : {A : Type} → (⊤ → A) ↔ A
law^1 = (λ f → f tt) , (λ a _ → a)

law1^ : {A : Type} → (A → ⊤) ↔ ⊤
law1^ = (λ _ → tt) , (λ _ _ → tt)

-- -- Some additional bonus/harder exercises:

-- -- ¬  \neg
-- -- An element of the type   ¬ A   means that the type A is empty.

-- ¬ : Type → Type
-- ¬ A = A → ⊥

-- ¬⊥ : ¬ ⊥
-- ¬⊥ = {!!}

-- ¬¬⊤ : ¬ (¬ ⊤)
-- ¬¬⊤ = {!!}

-- ¬¬-return : {A : Type} → A → ¬ (¬ A)
-- ¬¬-return = {!!}

-- ¬¬¬→¬ : {A : Type} → ¬ (¬ (¬ A)) → ¬ A
-- ¬¬¬→¬ = {!!}

-- -- Can you define a function with the following type?
-- dne : {A : Type} → ¬ (¬ A) → A
-- dne = {!!}
