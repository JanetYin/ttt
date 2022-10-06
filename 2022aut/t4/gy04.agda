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

-- in Haskell : Either A B, Left, Right

--   A ⊎ B

-- inl : A → A ⊎ B
-- inr : B → A ⊎ B

-- elimination by pattern matching

exSum₁ exSum₂ : ℕ ⊎ Bool
exSum₁ = inl 42
exSum₂ = inr false

getSum : ℕ ⊎ Bool → ℕ
getSum (inl x) = x
getSum (inr y) = if y then 1 else 0

-- getSum exSum₁ = ?
-- getSum exSum₂ = ?

select : {A B : Type} → Bool → A → B → A ⊎ B
select x a b = if x then inl a else inr b

-- select true a b = inl a

flipSum : {A B : Type} → A ⊎ B → B ⊎ A
flipSum (inl a) = inr a
flipSum (inr b) = inl b

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

-- ⊤ \top
-- ⊥ \bot

--  Empty tuple () in Haskell
-- ⊤ : type with 1 element tt
--  _×_ : binary product
--  ⊤   : nullary product

-- ↔  \lr

-- (A ↔ B) = (A → B) × (B → A)

example : ∀ {A : Type} → A ↔ (⊤ → A)
example = (λ a _ → a)
        , λ f → f _

-- Define an isomorphism between  Bool  and  ⊤ ⊎ ⊤

--  true       false    : Bool
--  inl tt     inr tt   : ⊤ ⊎ ⊤

from-Bool : Bool → ⊤ ⊎ ⊤
from-Bool true = inl tt
from-Bool false = inr tt

to-Bool : ⊤ ⊎ ⊤ → Bool
to-Bool (inl _) = true
to-Bool (inr _) = false

-- ⊥ : type with 0 elements
--  _⊎_ : binary sum
--  ⊥   : nullary sum

-- elimination  :  exfalso

-- for every  x : ⊥
--            A : Type
--------------------------------------------------------------------------------
--            exfalso x : A

exfalso-Bool : ⊥ → Bool
exfalso-Bool x = exfalso x

-- Define an element with the following type
example-⊥ : (⊤ → ⊥) ⊎ (⊥ → ⊤)
example-⊥ = inr (λ x → tt)

-- A ↔ B = (A → B) × (B → A)

-- -- (⊎, ⊥) form a commutative monoid (kommutativ egysegelemes felcsoport)

-- assoc⊎ : {A B C : Set} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C)
-- assoc⊎ = {!!}

-- idl⊎ : {A : Set} → ⊥ ⊎ A ↔ A
-- idl⊎ = {!!}

-- idr⊎ : {A : Set} → A ⊎ ⊥ ↔ A
-- idr⊎ = {!!}

-- comm⊎ : {A B : Set} → A ⊎ B ↔ B ⊎ A
-- comm⊎ = {!!}

-- -- (×, ⊤) form a commutative monoid (kommutativ egysegelemes felcsoport)

-- assoc× : {A B C : Set} → (A × B) × C ↔ A × (B × C)
-- assoc× = {!!}

-- idl× : {A : Set} → ⊤ × A ↔ A
-- idl× = {!!}

-- idr× : {A : Set} → A × ⊤ ↔ A
-- idr× = {!!}

-- -- ⊥ is a null element

-- null× : {A : Set} → A × ⊥ ↔ ⊥
-- null× = {!!}

-- -- distributivity of × and ⊎

-- dist : {A B C : Set} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
-- dist = {!!}

-- -- exponentiation laws

-- curry : ∀{A B C : Set} → (A × B → C) ↔ (A → B → C)
-- curry = {!!}

-- ⊎×→ : {A B C D : Set} → ((A ⊎ B) → C) ↔ (A → C) × (B → C)
-- ⊎×→ = {!!}

-- law^0 : {A : Set} → (⊥ → A) ↔ ⊤
-- law^0 = {!!}

-- law^1 : {A : Set} → (⊤ → A) ↔ A
-- law^1 = {!!}

-- law1^ : {A : Set} → (A → ⊤) ↔ ⊤
-- law1^ = {!!}
