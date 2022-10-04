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

-- ⊤ : type with 1 element
--  _×_ : binary product
--  ⊤   : nullary product

-- from-Bool and to-Bool should be inverses.
from-Bool : Bool → ⊤ ⊎ ⊤
from-Bool = {!!}

to-Bool : ⊤ ⊎ ⊤ → Bool
to-Bool = {!!}

-- A ↔ B = (A → B) × (B → A)
-- A logical equivalence f : A ↔ B consists of functions
--  fst f : A → B, and
--  snd f : B → A

Bool↔⊤⊎⊤ : Bool ↔ ⊤ ⊎ ⊤
Bool↔⊤⊎⊤ = from-Bool , to-Bool

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

example-⊥ : (⊤ → ⊥) ⊎ (⊥ → ⊤)
example-⊥ = {!!}

-- Algebraic laws

-- (⊎, ⊥) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc⊎ : {A B C : Set} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C)
assoc⊎ = {!!}

idl⊎ : {A : Set} → ⊥ ⊎ A ↔ A
idl⊎ = {!!}

idr⊎ : {A : Set} → A ⊎ ⊥ ↔ A
idr⊎ = {!!}

comm⊎ : {A B : Set} → A ⊎ B ↔ B ⊎ A
comm⊎ = {!!}

-- (×, ⊤) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc× : {A B C : Set} → (A × B) × C ↔ A × (B × C)
assoc× = {!!}

idl× : {A : Set} → ⊤ × A ↔ A
idl× = {!!}

idr× : {A : Set} → A × ⊤ ↔ A
idr× = {!!}

-- ⊥ is a null element

null× : {A : Set} → A × ⊥ ↔ ⊥
null× = {!!}

-- distributivity of × and ⊎

dist : {A B C : Set} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
dist = {!!}

-- exponentiation laws

curry' : ∀{A B C : Set} → (A × B → C) ↔ (A → B → C)
curry' = {!!}

⊎×→ : {A B C D : Set} → ((A ⊎ B) → C) ↔ (A → C) × (B → C)
⊎×→ = {!!}

law^0 : {A : Set} → (⊥ → A) ↔ ⊤
law^0 = {!!}

law^1 : {A : Set} → (⊤ → A) ↔ A
law^1 = {!!}

law1^ : {A : Set} → (A → ⊤) ↔ ⊤
law1^ = {!!}


-- Some additional bonus/harder exercises:

-- ¬  \neg
-- An element of the type   ¬ A   means that the type A is empty.

¬ : Type → Type
¬ A = A → ⊥

¬⊥ : ¬ ⊥
¬⊥ = {!!}

¬¬⊤ : ¬ (¬ ⊤)
¬¬⊤ = {!!}

¬¬-return : {A : Type} → A → ¬ (¬ A)
¬¬-return = {!!}

¬¬¬→¬ : {A : Type} → ¬ (¬ (¬ A)) → ¬ A
¬¬¬→¬ = {!!}

-- Can you define a function with the following type?
dne : {A : Type} → ¬ (¬ A) → A
dne = {!!}
