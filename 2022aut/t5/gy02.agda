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
and = {!!}

or : Bool → Bool → Bool
or = {!!}

-- Define a function  add-or-mult : Bool → ℕ → ℕ → ℕ
--  such that  add-or-mult true n m = n + m
--       and   add-or-mult false n m = n * m  for every n, m : ℕ
add-or-mult : Bool → ℕ → ℕ → ℕ
add-or-mult = {!!}

-- Define as many different functions of type  Bool → Bool  as you can:
f1 f2 f3 f4 f5 : Bool → Bool
f1 = {!!}
f2 = {!!}
f3 = {!!}
f4 = {!!}
f5 = {!!}

-- Define as many different functions of type  Bool → Bool → Bool  as you can:
g1 g2 g3 g4 g5 : Bool → Bool → Bool
g1 = {!!}
g2 = {!!}
g3 = {!!}
g4 = {!!}
g5 = {!!}

-- Define as many different functions of type  (Bool → Bool) → Bool  as you can:
h1 h2 h3 h4 h5 : (Bool → Bool) → Bool
h1 = {!!}
h2 = {!!}
h3 = {!!}
h4 = {!!}
h5 = {!!}

-- Polymorphism

id : {A : Type} → A → A
id x = x

idℕ : ℕ → ℕ
idℕ = {!!}

idBool : Bool → Bool
idBool = {!!}

idℕ→ℕ : (ℕ → ℕ) → (ℕ → ℕ)
idℕ→ℕ = {!!}

const : {A B : Type} → A → B → A
const = {!!}

infixl 5 _∘_ -- Function composition associates to the left
_∘_ : {A B C : Type} → (B → C) → (A → B) → (A → C)
_∘_ = {!!}

once : {A : Type} → (A → A) → A → A
once = {!!}

twice : {A : Type} → (A → A) → A → A
twice = {!!}

ex1 = twice add3 1
-- What is the type of ex1 ?
-- What is the value of ex1 ?

ex2 = twice twice add3 1
-- What is the type of ex2 ?
-- What is the value of ex2 ? why ?
