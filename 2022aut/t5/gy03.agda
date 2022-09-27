module t5.gy03 where
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


-- Product types

--  Pairing        x , y
--  Projections    fst p    or  p .fst
--                 snd p    or  p .snd
--  Computation    fst (x , y) = x
--                 snd (x , y) = y

-- \times

ex : ℕ × Bool
ex = 2 , false

ex₁ : ℕ
-- ex₁ = fst ex
ex₁ = ex .fst

ex₂ : Bool
-- ex₂ = snd ex
ex₂ = ex .snd

-- Pattern matching :
add' : ℕ × ℕ → ℕ
add' (n , m) = n + m




flipℕ×Bool : ℕ × Bool → Bool × ℕ
flipℕ×Bool = {!!}


flip : {A B : Type} → A × B → B × A
flip = {!!}

flipTest₁ : flip (1 , 2) ≡ (2 , 1); flipTest₁ = refl


proj : {A B C : Type} → A × B × C → B
proj = {!!}


and' : Bool × Bool → Bool
and' = {!!}


if' : {A : Type} → Bool × A × A → A
if' = {!!}

-- from-prod and to-prod should be inverses.
--   from-prod (to-prod x) = x
--   to-prod (from-prod x) = x

from-prod : {A : Type} → A × A → (Bool → A)
from-prod = {!!}

to-prod : {A : Type} → (Bool → A) → A × A
to-prod = λ f → {!!}


-- curry and uncurry should be inverses.
curry : {A B C : Type} → (A × B → C) → (A → B → C)
curry = {!!}

uncurry : {A B C : Type} → (A → B → C) → (A × B → C)
uncurry = {!!}

-- Sum types

exSum₁ exSum₂ : ℕ ⊎ Bool
exSum₁ = inl 42
exSum₂ = inr false

getSum : ℕ ⊎ Bool → ℕ
getSum (inl x) = x
getSum (inr y) = if y then 1 else 0

-- getSum exSum₁ = ?
-- getSum exSum₂ = ?

select : {A B : Type} → Bool → A → B → A ⊎ B
select = {!!}

flipSum : {A B : Type} → A ⊎ B → B ⊎ A
flipSum = {!!}

-- Both  Bool × Bool  and  Bool ⊎ Bool  have 4 elements.
-- Define a bijection between them.
Bool×Bool→Bool⊎Bool : Bool × Bool → Bool ⊎ Bool
Bool×Bool→Bool⊎Bool = {!!}

Bool⊎Bool→Bool×Bool : Bool ⊎ Bool → Bool × Bool
Bool⊎Bool→Bool×Bool = {!!}

-- ⊤ and ⊥

-- ⊤ : type with 1 element
--  _×_ : binary product
--  ⊤   : nullary product

-- from-Bool and to-Bool should be inverses.
from-Bool : Bool → ⊤ ⊎ ⊤
from-Bool = {!!}

to-Bool : ⊤ ⊎ ⊤ → Bool
to-Bool = {!!}

Bool↔⊤⊎⊤ : Bool ↔ ⊤ ⊎ ⊤
Bool↔⊤⊎⊤ = from-Bool , to-Bool

-- ⊥ : type with 0 elements
--  _⊎_ : binary sum
--  ⊥   : nullary sum

-- elimination  :  exfalso

exfalso-Bool : ⊥ → Bool
exfalso-Bool x = exfalso x

example-⊥ : (⊤ → ⊥) ⊎ (⊥ → ⊤)
example-⊥ = {!!}

--------------------------------------------------------------------------------
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
