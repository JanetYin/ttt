module tut1 where

open import lib

-- 1. git clone
--       https://bitbucket.org/akaposi/ttt
-- 2. Alt+F2 "emacs"
-- 3. Create a file "ttt/tut1.agda"
-- 4. Typecheck with "C-c C-l"
--      -> the file should be colored

-- Emacs key bindings (C = Ctrl, M = Alt):
-- C-x C-f : create or open a file
-- C-x C-c : close Emacs
-- M-w : Copy
-- C-y : Paste
--
-- Agda-mode key bindings:
-- C-c C-l : Typecheck
-- C-c C-n : Evaluate

b1 b2 : Bool
b1 = true

-- Try to write other terms of type Bool !

b2 = if b1 then b1 else b1

-- Try to evaluate them with "C-c C-n"
-- C-c C-n b1
--   true
-- C-c C-n b2
--   true

-- λ = \lambda
-- λ x -> x

id : Bool -> Bool
id = λ x -> x

not : Bool -> Bool
not = λ x -> if x then false else true

id' : Bool -> Bool
id' = λ x → not (not x)

id'' : Bool -> Bool
id'' = λ x -> if x then x else x

-- id, id', id'' have the same behaviour, but are not equal

-- Functions with multiple arguments / Currying :
--   "Bool -> Bool -> Bool" = "Bool -> (Bool -> Bool)"

and : Bool -> Bool -> Bool
-- and = λ x -> (λ y -> if x then y else false)
and = λ x y -> if x then y else false
or = λ x y -> not (and (not x) (not y))

f : (Bool -> Bool) -> Bool
f = λ g -> g false

-- "f id" is not equal to "f not"
-- => id does not have the same behaviour as not

T F : Bool -> Bool
T = λ x -> true
F = λ x -> false

-- The only functions of type "Bool -> Bool" up to behaviour are id, not, T and F
-- Try to construct "g : (Bool -> Bool) -> Bool" such that
--   "g id = g T", "g not = g F" and "g id" is not equal to "g not"

g : (Bool -> Bool) -> Bool
g = λ f -> f true

