module t4.gy04 where
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

-- Elements of Bool × Bool
--   (true , true)
--   (true , false)
--   (false , true)
--   (false , false)

-- Elements of Bool ⊎ Bool
--   inl true
--   inl false
--   inr true
--   inr false

-- Define an isomorphism between them.
Bool×Bool→Bool⊎Bool : Bool × Bool → Bool ⊎ Bool
Bool×Bool→Bool⊎Bool = {!!}

Bool⊎Bool→Bool×Bool : Bool ⊎ Bool → Bool × Bool
Bool⊎Bool→Bool×Bool = {!!}

-- ⊤ and ⊥

-- ⊤ : type with 1 element
--  _×_ : binary product
--  ⊤   : nullary product

-- Define an isomorphism between  Bool  and  ⊤ ⊎ ⊤
from-Bool : Bool → ⊤ ⊎ ⊤
from-Bool = {!!}

to-Bool : ⊤ ⊎ ⊤ → Bool
to-Bool = {!!}

-- ⊥ : type with 0 elements
--  _⊎_ : binary sum
--  ⊥   : nullary sum

-- elimination  :  exfalso

exfalso-Bool : ⊥ → Bool
exfalso-Bool x = exfalso x

-- Define an element with the following type
example-⊥ : (⊤ → ⊥) ⊎ (⊥ → ⊤)
example-⊥ = {!!}

-- A ↔ B = (A → B) × (B → A)

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

curry : ∀{A B C : Set} → (A × B → C) ↔ (A → B → C)
curry = {!!}

⊎×→ : {A B C D : Set} → ((A ⊎ B) → C) ↔ (A → C) × (B → C)
⊎×→ = {!!}

law^0 : {A : Set} → (⊥ → A) ↔ ⊤
law^0 = {!!}

law^1 : {A : Set} → (⊤ → A) ↔ A
law^1 = {!!}

law1^ : {A : Set} → (A → ⊤) ↔ ⊤
law1^ = {!!}
