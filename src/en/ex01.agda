module en.ex01 where

open import Lib hiding (add)

-- 1. git clone https://bitbucket.org/akaposi/ttt
-- 2. Open this file (PATH) in emacs. (On the lab computers: Alt-F2 "emacs")
-- 3. Typecheck with "C-c C-l"
--      -> the file should now be colored

-- Emacs key bindings (C = Ctrl, M = Alt):
--  C-x C-f : create or open a file
--  C-x C-w : save (write) file
--  C-x C-s : save already named file
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

{-
-- Already expected knowledge, prerequisites for the subject:

+ Syntax of Haskell, Haskell language, types, usage of ghci
  + existing basic functions, operators
    + On numbers: _+_, _*_
    + On Booleans: not, (&&), (||), branching
    + On lists: head, tail, length, replicate, (!!), take, drop, map, filter, zip, zipWith, takeWhile, dropWhile
    + On tuples: (,), fst, snd
    + On Either type: Left, Right -- If unfamiliar, no problem, can be inspected in Haskell with :i.
  + binding strength of operators
  + recursion!
  + pattern matching!!
    + constructors
      + data constructors: Just, Nothing, True, False, [], (:), (,), Left, Right
      + type constructors: Maybe, Either, (->)
  + partial application, e.g., (1 +), (+ 2), (+) 3, (`mod` 5), (mod 5)
  + anonymous functions (there will be a short review): \x -> x + 1; \x y -> x * 2 - y
  + Type System:
    + Basic types notation, e.g., Int -> Int; a -> b -> a; Eq a => a -> [a] -> Bool
    + Polymorphism -> Parametric specifically; little will be said about ad-hoc.
    + Higher-order functions notation, e.g., (a -> b) -> [a] -> [b]; (a -> Bool) -> [a] -> [a]

Concepts:
  + partial/**total** function
  + recursion
  + partial/total application
  + Principle of currying, every function is unary, \x y -> x + 2 * y ≡ \x -> \y -> x + 2 * y

(Will be discussed) Very beginning of Group Theory: semigroup, monoid with identity element
(Will be discussed, these need to be known by the end of the subject) Properties: associativity, commutativity, identity, distributivity, symmetry, reflexivity, transitivity

-}

-- TODAY:
-- review; how to haskell in agda
-- learning agda's keycombinations
--  base type ℕ
--  function types   A → B
--   where A and B are any types
--   definitional equality


add3 : {!   !}
add3 = {!   !}

-- spaces matter!

-- C-c C-n  add3 4

aNum : ℕ
aNum = {! add3 4 !}

-- equational reasoning
-- aNum = add3 4
--      = 4 + 3
--      = 7

-- DO NOT write brackets in "add3(4)"

-- C-c C-n aNum

bNum : ℕ
bNum = add3 (add3 (add3 2))

-- "add3 add3 add3 2" is wrong

-- C-c C-n bNum

-- lambda notation

-- Meaning of defintional equality
add3' : ℕ → ℕ
add3' = {!!}
-- add3 x = x + 3

-- add3' 4 = (λ x → x + 3) 4
--         = (x + 3)[x := 4]
--         = (4 + 3)
--         = 7

-- test it with C-c C-n!

-- Partial application, just like in haskell (kind of)
add4 : ℕ → ℕ
add4 = {!!}

-- Goal type and context:             C-c C-,
-- Goal type, context, inferred type: C-c C-.
-- Fill the hole                    : C-c C-space  ,  C-c C-r
-- Creating a hole: enter '?'

-- functions with multiple arguments

add : ℕ → ℕ → ℕ
add = {!!}

-- ℕ → (ℕ → ℕ) = ℕ → ℕ → ℕ
--             ≠ (ℕ → ℕ) → ℕ
-- bracketing of λ

-- same as λ x → λ y → x + y
-- same as λ x y → x + y

add3'' : ℕ → ℕ
add3'' = add 3

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



tw : {A : Set} → (A → A) → A → A
tw f n = f (f n)

-- consider

t = tw tw add3 1
-- what is the type of this and why? ask Agda too (C-c C-d).
-- what is its value?  guess, and ask Agda too (C-c C-n).

first : {A : Set} → A → A → A
first = {!!}

second : {A : Set} → A → A → A
second = {!!}

----------------------------------------------

-- Show definitional equality meaning on Bools:
-- constTrue with pattern matching
-- constTrue normally
-- C-c C-n try (λ x → constTrue x), see what happens in each case!
