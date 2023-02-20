module t5.gy02 where
open import lib

-- 1. git clone https://bitbucket.org/akaposi/ttt
-- 2. Open this file (2022aut/t5/gy02.agda) in emacs. (On the lab computers: Alt-F2 "emacs")
-- 3. Typecheck with "C-c C-l"
--      -> the file should now be colored

-- Emacs key bindings (C = Ctrl, M = Alt):
--  C-x C-f : create or open a file
--  C-x C-w : save (write) file
--  C-x C-c : close Emacs
--  C-space : start selecting text
--  M-w : Copy
--  C-w : Cut
--  C-y : Paste

-- Agda-mode key bindings:
--  C-\       : Switch Agda input mode on/off
--  C-c C-l   : Typecheck the current file
--  C-c C-n   : Normalise an expression (reduce the expression as much as possible)
--  C-c C-d   : Deduce the type of an expression
--  C-c C-,   : Show the goal type and context of a hole
--                (C-u C-u C-c C-, : same but fully normalise the goal
--                 C-u C-c C-,     : same but do not normalise the goal)
--  C-c C-.   : Goal type and context + inferred type of current expression
--  C-c C-SPC : Fill goal
--  C-c C-x = : Describe character at point

-- List of unicode symbols:
--    →       \to
--            \rightarrow
--    ℕ       \bN           'b'lackboard 'N', there is also \bZ for ℤ, etc
--    λ       \Gl           'G'reek 'l', there is also \GG for Γ, etc
--            \lambda

-- Tests:
add3 : ℕ → ℕ
add3 n = n + 3

-- There will be automated tests in the homework and assignments, with the following format:
--  (The equality type _≡_ will be explained later in the semester)
add3_test1 : add3 5 ≡ 8 ; add3_test1 = refl
add3_test2 : add3 0 ≡ 3 ; add3_test2 = refl

-- Booleans

-- Type:           Bool
-- "Constructors"  true : Bool  false : Bool   (introduction)
-- "Eliminator"    if_then_else_

              --       b : Bool      u : A      v : A
              -------------------------------------------
              --         if b then u else v : A

-- Computation:
--   if true  then u else v = u
--   if false then u else v = v

aBool : Bool
aBool = true

bBool : Bool
bBool = false

cBool : Bool
cBool = if aBool then true else false

not : Bool → Bool
not = λ b → if b then false else true

-- Define the functions 'and' and 'or' using if_then_else_:
and : Bool → Bool → Bool
-- and x y = if x then y else false -- A = Bool
-- and x y = if y then x else false
and x = if x then (λ y → y) else (λ y → false) -- A = Bool → Bool

or : Bool → Bool → Bool
-- or = λ x y → if x then true else y
or x y = not (and (not x) (not y))

-- Define a function  add-or-mult : Bool → ℕ → ℕ → ℕ
--  such that  add-or-mult true n m = n + m
--       and   add-or-mult false n m = n * m  for every n, m : ℕ
add-or-mult : Bool → ℕ → ℕ → ℕ
add-or-mult b = if b then _+_ else _*_
-- if_then_else_

b1 b2 : Bool
b1 = true
b2 = false

-- Define as many different functions of type  Bool → Bool  as you can:
f1 f2 f3 f4 f5 : Bool → Bool
f1 = not
f2 b = true
f3 b = false
f4 b = b
f5 b = not (not (not b)) -- f5 = f1

f : Bool → Bool
f b = if b then {!!} else {!!}
-- two choices for ?0
-- two choices for ?1

-- Define as many different functions of type  Bool → Bool → Bool  as you can:
g1 g2 g3 g4 g5 : Bool → (Bool → Bool)
g1 = and
g2 = or
g3 = λ _ _ → true
g4 = λ x _ → x
g5 = λ x y → not y
-- ...

--      Bool           →         (Bool → Bool)
--       ^ 2 elements                  ^ 4 elements

g : Bool → (Bool → Bool)
g b = if b then {!!} else {!!}
-- 4 choices for ?2
-- 4 choices for ?3

-- 16 possible definitions

--   A                  → B
--    na elements         nb elements

--   A → B  has "nb to the power na" elements


-- Define as many different functions of type  (Bool → Bool) → Bool  as you can:
h1 h2 h3 h4 h5 : (Bool → Bool) → Bool
h1 = {!!}
h2 = {!!}
h3 = {!!}
h4 = {!!}
h5 = {!!}

-- 2^4 = 16 elements of type (Bool → Bool) → Bool
h : (Bool → Bool) → Bool
h f = if f true
      then (if f false then {!!} else {!!})
      else (if f false then {!!} else {!!})

-- Polymorphism
-- In Haskell:
--   id :: a -> a
--   id :: forall a. a -> a

id : {A : Type} → A → A
id x = x
-- Hard question: how many elements of type {A : Type} → A → A
--  can you define ?

idℕ : ℕ → ℕ
idℕ n = id {A = ℕ} n

-- Agda is solving the equation   A → A   =?   Bool → Bool
--                 only solution  A := Bool
idBool : Bool → Bool
idBool = id

idℕ→ℕ : (ℕ → ℕ) → (ℕ → ℕ)
idℕ→ℕ = id {ℕ → ℕ}

id' : ℕ → ℕ
id' n = id {(ℕ → ℕ) → (ℕ → ℕ)} (id {ℕ → ℕ}) (id {ℕ}) n
-- id id id 5 = (((id id) id) 5)
--            = (id id) 5
--            = id 5
--            = 5

const : {A B : Type} → A → B → A
const x y = x

infixl 5 _∘_ -- Function composition associates to the left
_∘_ : {A B C : Type} → (B → C) → (A → B) → (A → C)
-- _∘_ f g x = f (g x)
(f ∘ g) x = f (g x)

once : {A : Type} → (A → A) → A → A
once f x = f x

twice : {A : Type} → (A → A) → A → A
twice f x = f (f x)

ex1 = twice add3 1
-- What is the type of ex1 ?
-- What is the value of ex1 ?

ex2 = twice twice add3 1
-- What is the type of ex2 ?
-- What is the value of ex2 ? why ?
