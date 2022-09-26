module t4.gy03 where
open import lib

-- Polymorphism

-- In Haskell:
--       id :: a -> a
--       id :: forall a. a -> a

id : {A : Type} → A → A
id x = x

idℕ : ℕ → ℕ
idℕ = id {A = ℕ}

idBool : Bool → Bool
idBool = id

idℕ→ℕ : (ℕ → ℕ) → (ℕ → ℕ)
idℕ→ℕ = id

const : {A B : Type} → A → B → A
const = {!!}

-- infixl 5 _∘_ -- Function composition associates to the left
-- _∘_ : {A B C : Type} → (B → C) → (A → B) → (A → C)
-- _∘_ = {!!}

-- once : {A : Type} → (A → A) → A → A
-- once = {!!}

-- twice : {A : Type} → (A → A) → A → A
-- twice = {!!}

-- ex1 = twice add3 1
-- -- What is the type of ex1 ?
-- -- What is the value of ex1 ?

-- ex2 = twice twice add3 1
-- -- What is the type of ex2 ?
-- -- What is the value of ex2 ? why ?

-- Product types

--  Pairing        x , y
--  Projections    fst p
--                 snd p
--  Computation    fst (x , y) = x
--                 snd (x , y) = y

ex : ℕ × Bool
ex = 2 , false

ex₁ : ℕ
-- ex₁ = fst ex
ex₁ = ex .fst

ex₂ : Bool
-- ex₂ = snd ex
ex₂ = ex .snd


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


from-prod : {A : Type} → A × A → (Bool → A)
from-prod = {!!}

to-prod : {A : Type} → (Bool → A) → A × A
to-prod = λ f → {!!}


curry : {A B C : Type} → (A × B → C) → (A → B → C)
curry = {!!}

uncurry : {A B C : Type} → (A → B → C) → (A × B → C)
uncurry = {!!}

-- Pattern matching
add' : ℕ × ℕ → ℕ
add' (n , m) = n + m

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
-- Define an isomorphism between them.
Bool×Bool→Bool⊎Bool : Bool × Bool → Bool ⊎ Bool
Bool×Bool→Bool⊎Bool = {!!}

Bool⊎Bool→Bool×Bool : Bool ⊎ Bool → Bool × Bool
Bool⊎Bool→Bool×Bool = {!!}

-- ⊤ and ⊥

-- ⊤ : type with 1 element
--  _×_ : binary product
--  ⊤   : nullary product

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

example-⊥ : (⊤ → ⊥) ⊎ (⊥ → ⊤)
example-⊥ = {!!}
