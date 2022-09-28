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
--    ₁       \_1
--    ₐ       \_a
--    ¹       \^1


-- Product types

-- types A B         --->    A × B
-- type of pairs of an element of A and an element of B

--  Pairing        x , y
--  Projections    fst p    or  p .fst    where p : A × B
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
-- add' p = fst p + snd p


flipℕ×Bool : ℕ × Bool → Bool × ℕ
-- flipℕ×Bool = λ p → p .snd , p .fst
flipℕ×Bool (x , y) = y , x


flip : {A B : Type} → A × B → B × A
flip (x , y) = y , x

flipTest₁ : flip (1 , 2) ≡ (2 , 1); flipTest₁ = refl

-- A × B × C = A × (B × C)
proj : {A B C : Type} → A × (B × C) → B
-- proj (x , y , z) = y
-- proj = λ p → p .snd .fst
proj p = fst (snd p)

-- uncurried "and" and "if"
and' : Bool × Bool → Bool
and' (x , y) = if x then y else false

if' : {A : Type} → Bool × A × A → A
-- if' (x , y , z) = if_then_else_ x y z
if' (x , y , z) = if x then y else z


-- from-prod and to-prod should be inverses.
--   from-prod (to-prod x) = x
--   to-prod (from-prod x) = x

-- p : A × A     contains two elements   p .fst   and   p .snd
-- f : Bool → A  contains two elements   f false  and   f true

-- if A has n elements
--   A × A    has n*n elements
--   Bool → A has n^2 elements

from-prod : {A : Type} → A × A → (Bool → A)
from-prod (x , y) b = if b then y else x

to-prod : {A : Type} → (Bool → A) → A × A
to-prod = λ f → f false , f true



-- curry and uncurry should be inverses.
curry : {A B C : Type} → (A × B → C) → (A → B → C)
curry = λ f a b → f (a , b)

uncurry : {A B C : Type} → (A → B → C) → (A × B → C)
uncurry = λ f p → f (p .fst) (p .snd)

--  (nc^nb)^na   =  nc^(nb * na)
--  (A → B → C)  ≅  (A × B → C)

-- Sum types

-- \u+

-- Type          A ⊎ B
-- Contructors   inl : A → A ⊎ B
--               inr : B → A ⊎ B

exSum₁ exSum₂ : ℕ ⊎ Bool
exSum₁ = inl 42
exSum₂ = inr false

getSum : ℕ ⊎ Bool → ℕ
getSum (inl x) = x + 3
getSum (inr y) = if y then 1 else 0

getSum' : ℕ ⊎ Bool → ℕ
getSum' x = {!!} -- C-c C-c    x ENTER  :  Case splitting

somefunction : ℕ × Bool → ℕ
somefunction p = {!!} -- C-c C-c    p ENTER  :  Case splitting

-- getSum exSum₁ = ?
-- getSum exSum₂ = ?

select : {A B : Type} → Bool → A → B → A ⊎ B
select b x y = if b then inl x else inr y

-- select false   should use   inl
-- select true    should use   inr

flipSum : {A B : Type} → A ⊎ B → B ⊎ A
flipSum (inl x) = inr x
flipSum (inr x) = inl x
--    na + nb = nb + na

-- Both  Bool × Bool  and  Bool ⊎ Bool  have 4 elements.
-- Define a bijection between them.
Bool×Bool→Bool⊎Bool : Bool × Bool → Bool ⊎ Bool
-- Bool×Bool→Bool⊎Bool = λ p → if p .fst then inl (p .snd) else inr (p .snd)
Bool×Bool→Bool⊎Bool = λ p → (if p .fst then inl else inr) (p .snd)

Bool⊎Bool→Bool×Bool : Bool ⊎ Bool → Bool × Bool
Bool⊎Bool→Bool×Bool (inl x) = true , x
Bool⊎Bool→Bool×Bool (inr x) = false , x

-- -- ⊤ and ⊥

-- -- ⊤ : type with 1 element
-- --  _×_ : binary product
-- --  ⊤   : nullary product

-- -- from-Bool and to-Bool should be inverses.
-- from-Bool : Bool → ⊤ ⊎ ⊤
-- from-Bool = {!!}

-- to-Bool : ⊤ ⊎ ⊤ → Bool
-- to-Bool = {!!}

-- Bool↔⊤⊎⊤ : Bool ↔ ⊤ ⊎ ⊤
-- Bool↔⊤⊎⊤ = from-Bool , to-Bool

-- -- ⊥ : type with 0 elements
-- --  _⊎_ : binary sum
-- --  ⊥   : nullary sum

-- -- elimination  :  exfalso

-- exfalso-Bool : ⊥ → Bool
-- exfalso-Bool x = exfalso x

-- example-⊥ : (⊤ → ⊥) ⊎ (⊥ → ⊤)
-- example-⊥ = {!!}

--------------------------------------------------------------------------------
-- Algebraic laws

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

-- curry' : ∀{A B C : Set} → (A × B → C) ↔ (A → B → C)
-- curry' = {!!}

-- ⊎×→ : {A B C D : Set} → ((A ⊎ B) → C) ↔ (A → C) × (B → C)
-- ⊎×→ = {!!}

-- law^0 : {A : Set} → (⊥ → A) ↔ ⊤
-- law^0 = {!!}

-- law^1 : {A : Set} → (⊤ → A) ↔ A
-- law^1 = {!!}

-- law1^ : {A : Set} → (A → ⊤) ↔ ⊤
-- law1^ = {!!}
