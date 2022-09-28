module t4.gy03 where
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

-- Polymorphism

-- In Haskell:
--     id :: a -> a
--     id :: forall a. a -> a

id : {A : Type} → A → A
id x = x

idℕ : ℕ → ℕ
idℕ = id {A = ℕ}

idBool : Bool → Bool
idBool = id

idℕ→ℕ : (ℕ → ℕ) → (ℕ → ℕ)
idℕ→ℕ = id

const : {A B : Type} → A → B → A
const x y = x
-- x : A
-- y : B

infixl 5 _∘_ -- Function composition associates to the left
_∘_ : {A B C : Type} → (B → C) → (A → B) → (A → C)
--                                       → A → C
_∘_ f g x = f (g x)
--  x       : A
--  g x     : B
--  f (g x) : C

once : {A : Type} → (A → A) → A → A
--                           (A → A)
-- once f x = f x
-- once f = f
once = id

twice : {A : Type} → (A → A) → A → A
-- twice f x = f (f x)
twice f = f ∘ f

add3 = λ n → n + 3
ex1 = twice {A = ℕ} add3 1
-- What is the type of ex1 ?    ex1 : ℕ
-- What is the value of ex1 ?   1 + 3 + 3 = 7

ex2 = (twice {A = ℕ → ℕ} (twice {A = ℕ})) add3 1
-- What is the type of ex2 ?          ex2 : ℕ
-- What is the value of ex2 ? why ?   13
--                                    1 + 3 * (2 ^ 2)

-- twice twice : {A : Type} → (A → A) → A → A
--  apply a function 4 times

ex3 = twice (twice add3) 1
--                                    13 = 1 + 3 * (2 * 2)

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


flipℕ×Bool : ℕ × Bool → Bool × ℕ
-- flipℕ×Bool = λ p → p .snd , p .fst
-- flipℕ×Bool (x , y) = y , x

flipℕ×Bool (x , y) = y , x

-- C-c C-r in a hole with type A × B
--  ?0    is replaced with   ?1 , ?2

-- C-c C-c in a hole when p : A × B is bound
--    f p = ?0   is replaced by   f (x , y) = ?0

flip : {A B : Type} → A × B → B × A
flip = λ p → p .snd , p .fst

flipTest₁ : flip (1 , 2) ≡ (2 , 1); flipTest₁ = refl

-- A × B × C = A × (B × C)
proj : {A B C : Type} → A × B × C → B
proj = λ p → p .snd .fst
-- proj (x , y , z) = y


and' : Bool × Bool → Bool
and' (x , y) = if x then y else false


if' : {A : Type} → Bool × A × A → A
if' (b , x , y) = if_then_else_ b x y


-- from-prod and to-prod should be inverses.
--   from-prod (to-prod x) = x
--   to-prod (from-prod x) = x

from-prod : {A : Type} → A × A → (Bool → A)
from-prod (x , y) b = if b then x else y

to-prod : {A : Type} → (Bool → A) → A × A
to-prod = λ f → f true , f false


-- curry and uncurry should be inverses.
curry : {A B C : Type} → (A × B → C) → (A → B → C)
curry = λ f a b → f (a , b)

uncurry : {A B C : Type} → (A → B → C) → (A × B → C)
uncurry = λ f (a , b) → f a b

-- -- Pattern matching
-- add' : ℕ × ℕ → ℕ
-- add' (n , m) = n + m

-- -- Sum types

-- exSum₁ exSum₂ : ℕ ⊎ Bool
-- exSum₁ = inl 42
-- exSum₂ = inr false

-- getSum : ℕ ⊎ Bool → ℕ
-- getSum (inl x) = x
-- getSum (inr y) = if y then 1 else 0

-- -- getSum exSum₁ = ?
-- -- getSum exSum₂ = ?

-- select : {A B : Type} → Bool → A → B → A ⊎ B
-- select = {!!}

-- flipSum : {A B : Type} → A ⊎ B → B ⊎ A
-- flipSum = {!!}

-- -- Both  Bool × Bool  and  Bool ⊎ Bool  have 4 elements.
-- -- Define an isomorphism between them.
-- Bool×Bool→Bool⊎Bool : Bool × Bool → Bool ⊎ Bool
-- Bool×Bool→Bool⊎Bool = {!!}

-- Bool⊎Bool→Bool×Bool : Bool ⊎ Bool → Bool × Bool
-- Bool⊎Bool→Bool×Bool = {!!}

-- -- ⊤ and ⊥

-- -- ⊤ : type with 1 element
-- --  _×_ : binary product
-- --  ⊤   : nullary product

-- from-Bool : Bool → ⊤ ⊎ ⊤
-- from-Bool = {!!}

-- to-Bool : ⊤ ⊎ ⊤ → Bool
-- to-Bool = {!!}

-- -- ⊥ : type with 0 elements
-- --  _⊎_ : binary sum
-- --  ⊥   : nullary sum

-- -- elimination  :  exfalso

-- exfalso-Bool : ⊥ → Bool
-- exfalso-Bool x = exfalso x

-- example-⊥ : (⊤ → ⊥) ⊎ (⊥ → ⊤)
-- example-⊥ = {!!}
