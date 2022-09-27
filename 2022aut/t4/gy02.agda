module t4.gy02 where
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
--    𝔹       \bB
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

-- Type:           𝔹
-- "Constructors"  true : 𝔹
-- "Eliminator"    if_then_else_

                  --       b : 𝔹      u : A      v : A
                  -------------------------------------------
                  --         if b then u else v : A

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
-- and x y = if x then y else false
-- and x = if x then (λ y → y) else (λ y → false)
and x y = if y then x else false

or : Bool → Bool → Bool
or x y = if x then true else y
-- or x y = not (and (not x) (not y))

-- pattern matching:
--  or true  y = y
--  or false _ = false

-- Define a function  add-or-mult : Bool → ℕ → ℕ → ℕ
--  such that  add-or-mult true n m = n + m
--       and   add-or-mult false n m = n * m  for every n, m : ℕ
add-or-mult : Bool → ℕ → ℕ → ℕ
-- add-or-mult b = if b then _+_ else _*_
add-or-mult b n m = if b then n + m else n * m

-- Define as many different functions of type  Bool → Bool  as you can:
f1 f2 f3 f4 f5 : Bool → Bool
f1 = not
f2 = λ x → x
f3 = λ _ → true
f4 = λ _ → false
f5 = λ x → not (not (not (not x)))
-- f2 ≡ f5
-- Only 4 functions of type Bool → Bool
--  A function f : Bool → Bool is determined by  f true  and  f false

-- Define as many different functions of type  Bool → Bool → Bool  as you can:
g1 g2 g3 g4 g5 : Bool → Bool → Bool
g1 = and
g2 = or

-- g3 x y = if x then (if y then true else false) else (if y then true else false)
g3 x y = y

g4 = λ x y → x
g5 = λ x y → false

-- 16 possible functions Bool → Bool → Bool

-- Define as many different functions of type  (Bool → Bool) → Bool  as you can:
h1 h2 h3 h4 h5 : (Bool → Bool) → Bool
h1 f = true
h2 f = f true
h3 f = f false
h4 f = and (f true) (f false)
h5 f = f (f (f false))

-- h6 f = if f true then (if f false then {!!} else {!!})
--                  else (if f false then {!!} else {!!})
       -- only depends on   f true and f false

-- 16 possible functions of type (Bool → Bool) → Bool

-- If A has na elements and B has nb elements
--   then (A → B) has (nb ^ na) (nb to the power na) elements.

-- How many different functions are there of type  ((Bool → Bool) → Bool) → Bool ?
--  2 ^ 16 functions.

--  next week: Product types and Sum types.
--    A × B will have na * nb elements
--    A + B will have na + nb elements

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
const x y = x

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
