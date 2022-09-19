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

-- Booleans

-- Type:           𝔹
-- "Constructors"  true : 𝔹
-- "Eliminator"    if_then_else_

                  --       b : 𝔹      u : A      v : A
                  -------------------------------------------
                  --         if b then u else v : A

aBool : 𝔹
aBool = true

bBool : 𝔹
bBool = false

cBool : 𝔹
cBool = if aBool then true else false

not : 𝔹 → 𝔹
not = {!!}

-- Define the functions 'and' and 'or' using if_then_else_:
and : 𝔹 → 𝔹 → 𝔹
and = {!!}

or : 𝔹 → 𝔹 → 𝔹
or = {!!}

-- Define a function  add-or-mult : 𝔹 → ℕ → ℕ
--  such that  add-or-mult true n m = n + m   and   add-or-mult false n m = n * m  for every n, m : ℕ
add-or-mult : 𝔹 → ℕ → ℕ
add-or-mult = {!!}

-- Define as many different functions of type  𝔹 → 𝔹  as you can:
f1 f2 f3 f4 f5 : 𝔹 → 𝔹
f1 = not
f2 = {!!}
f3 = {!!}
f4 = {!!}
f5 = {!!}

-- Define as many different functions of type  𝔹 → 𝔹 → 𝔹  as you can:
g1 g2 g3 g4 g5 : 𝔹 → 𝔹 → 𝔹
g1 = and
g2 = or
g3 = {!!}
g4 = {!!}
g5 = {!!}


-- Define as many different functions of type  (𝔹 → 𝔹) → 𝔹  as you can:
h1 h2 h3 h4 h5 : 𝔹 → 𝔹 → 𝔹
h1 = {!!}
h2 = {!!}
h3 = {!!}
h4 = {!!}
h5 = {!!}
-- ...

-- How many different functions are there of type  ((𝔹 → 𝔹) → 𝔹) → 𝔹 ?

-- Polymorphism
id : {A : Type} → A → A
id = {!!}

idℕ : ℕ → ℕ
idℕ = id {ℕ}

id𝔹 : 𝔹 → 𝔹
id𝔹 = id

idℕ→ℕ : (ℕ → ℕ) → (ℕ → ℕ)
idℕ→ℕ = id

const : {A B : Type} → A → B → A
const = {!!}

infixl 5 _∘_ -- Function composition associates to the left
_∘_ : {A B C : Type} → (B → C) → (A → B) → (A → C)
_∘_ = {!!}

once : {A : Type} → (A → A) → A → A
once = {!!}

twice : {A : Type} → (A → A) → A → A
twice = {!!}

add3 : ℕ → ℕ
add3 n = n + 3

ex1 = twice add3 1
-- What is the type of ex1 ?
-- What is the value of ex1 ?

ex2 = twice twice add3 1
-- What is the type of ex2 ?
-- What is the value of ex2 ? why ?
