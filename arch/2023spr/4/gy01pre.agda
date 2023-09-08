open import Agda.Builtin.Nat renaming (Nat to ℕ)

-- 1. git clone https://bitbucket.org/akaposi/ttt
-- 2. Open this file (PATH) in emacs. (On the lab computers: Alt-F2 "emacs")
-- 3. Typecheck with "C-c C-l"
--      -> the file should now be colored

-- Emacs key bindings (C = Ctrl, M = Alt):
--  C-x C-f : create or open a file (find)
--  C-x C-s : save
--  C-x C-w : save as... (write)
--  C-x C-c : close Emacs
--  C-space : start selecting text
--  M-w : Copy
--  C-w : Cut
--  C-y : Paste (yank)

-- Agda-mode key bindings:
--  C-\       : Switch Agda input mode on/off
--  C-c C-l   : Typecheck the current file
--  C-c C-n   : Normalise an expression (reduce the expression as much as possible)
--  C-c C-d   : Deduce the type of an expression
--  C-c C-x = : Describe character at point (how to write it)
-- in holes:
--  C-c C-,   : Show the goal type and context of a hole
--                (C-u C-u C-c C-, : same but fully normalise the goal
--                 C-u C-c C-,     : same but do not normalise the goal)
--  C-c C-.   : Goal type and context + inferred type of current expression
--  C-c C-SPC : Fill goal

-- List of unicode symbols:
--    →       \r, \to, \rightarrow
--    ℕ       \bN           'b'lackboard 'N', there is also \bZ for ℤ, etc
--    λ       \Gl           'G'reek 'l', there is also \GG for Γ, etc

-- TODAY:
--  base type ℕ
--  function types   A → B
--   where A and B are any types

-- write ? and press C-c C-l to make a hole

add3 : ℕ → ℕ
add3 = {!!}

-- try add3 x = x+3, spaces matter!

-- C-c C-n  add3 4

aNum : ℕ
aNum = add3 4

-- equational reasoning
-- aNum = add3 4
--      = 4 + 3
--      = 7

-- no need to write brackets in "add3(4)"

-- C-c C-n aNum

bNum : ℕ
bNum = add3 (add3 (add3 2))

-- "add3 add3 add3 2" is wrong (try with C-c C-n)
-- why?

-- C-c C-n bNum

-- lambda notation

add3' : ℕ → ℕ
add3' = λ x → x + 3
-- add3 x = x + 3

-- add3' 4 = (λ x → x + 3) 4
--         = (x + 3)[x := 4]
--         = (4 + 3)
--         = 7

-- test it with C-c C-n!

add4 : ℕ → ℕ
add4 = {!!}

-- Goal type and context:                  C-c C-,
-- Goal type, context, inferred type:      C-c C-.
-- Fill the hole                    :      C-c C-space
-- Refine (automatically add plus holes) : C-c C-r
-- Creating a hole: enter '?' and press C-c C-l

-- functions with multiple arguments

add : ℕ → ℕ → ℕ
add = {!!}

-- ℕ → (ℕ → ℕ) = ℕ → ℕ → ℕ
--             ≠ (ℕ → ℕ) → ℕ
-- bracketing of λ

-- same as λ x → λ y → x + y (which means λ x → (λ y → x + y))
-- same as λ x y → x + y

-- currying
add3'' : ℕ → ℕ
add3'' = add 3

{-
add3'' = add 3 = (λ x → (λ y → x + y)) 3
               = (λ y → x + y)[ x := 3]
               = (λ y → 3 + y)
-}

num1 : ℕ
num1 = add 3 4

-- bracketing of application

num1' : ℕ
num1' = (add 3) 4

-- what is wrong with the following?

-- num2 : ℕ
-- num2 = add (3 4)

-- what is wrong with the following?

-- num3 : ℕ
-- num3 = add 3 (add 4)

-- compute with equational reasoning:

num4 : ℕ
num4 = add 3 (add 4 2)

-- Higher-order functions: functions with functions as arguments
-- e.g. in Haskell:   map :: (a -> b) -> [a] -> [b]

-- write a function of the following type:

f1 : (ℕ → ℕ) → ℕ
f1 = {!!}

-- test it with f1 add3, f1 add4. is the result the same?

-- write two different functions which use their inputs, i.e.
--   f2 add3 ≠ f2 add4 ≠ f3 add4 ≠ f3 add3

f2 f3 : (ℕ → ℕ) → ℕ
f2 = {!!}
f3 = {!!}

-- a polymorphic function
tw : {A : Set} → (A → A) → A → A  --apply a function twice
tw f n = f (f n)

-- consider

t = tw tw add3 1
-- what is the type of this and why? ask Agda too (C-c C-d).
-- what is its value?  guess, and ask Agda too (C-c C-n).

first : {A : Set} → A → A → A
first = {!!}

second : {A : Set} → A → A → A
second = {!!}

