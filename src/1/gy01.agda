module gy01 where

open import lib-gy01

{-
Követelmények:
∀ óra elején +/- (0/1 pont), 10 db, 5-10 perces.
NINCS ZH!!! mindenki örömére
Gyakorlásként házi feladatok lesznek (nem kötelező)

Vizsga: Kódolós, 10 feladat, 10 pont
2: 5-től
3: 7-től
4: 8-tól
5: 9-től
-}

-- 1. git clone https://bitbucket.org/akaposi/ttt
-- 2. Open this file (PATH) in emacs. (On the lab computers: Alt-F2 "emacs")
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

-- TODAY:
--  base type ℕ
--  function types   A → B
--   where A and B are any types

add3 : ℕ → ℕ
add3 n = n + 3

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

-- "add3 add3 add3 2" is wrong

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
add4 x = x + 4

-- Goal type and context:             C-c C-,
-- Goal type, context, inferred type: C-c C-.
-- Fill the hole                    : C-c C-space
-- Refine hole                      : C-c C-r
-- Creating a hole: enter '?'

-- functions with multiple arguments

add : ℕ → (ℕ → ℕ)
add = λ x y → x + y

add' : ℕ → ℕ → ℕ
add' x = λ y → x + y

-- ℕ → (ℕ → ℕ) = ℕ → ℕ → ℕ
--             ≠ (ℕ → ℕ) → ℕ
-- bracketing of λ

-- same as λ x → λ y → x + y
-- same as λ x y → x + y

add3'' : ℕ → ℕ
add3'' = add 3

add4'' : ℕ → ℕ
add4'' = add 4

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

{-
add : ℕ → (ℕ → ℕ)
add = λ x y → x + y

add 3 (add 4 2) = (add def)
add 3 ((λ x y → x + y) 4 2) = → β-redukció
add 3 ((x + y)[x := 4][y := 2]) = ([] def)
add 3 ((4 + y)[y := 2]) = ([] def)
add 3 (4 + 2) = (ált. isk.) (+ def)
add 3 6 = (add def)
(λ x y → x + y) 3 6 = → β-redukció
(x + y)[x := 3][y := 6]) = ([] def ×2)
3 + 6 = (ált. isk.) (+ def)
9
-}
-- Higher-order functions: functions with functions as arguments
-- e.g. in Haskell:   map :: (a -> b) -> [a] -> [b]

-- write a function of the following type:

f1 : (ℕ → ℕ) → ℕ
f1 _ = 42

-- test it with f1 add3, f1 add4. is the result the same?

-- write two different functions which use their inputs, i.e.
--   f2 add3 ≠ f2 add4 ≠ f3 add4 ≠ f3 add3

f2 f3 : (ℕ → ℕ) → ℕ
f2 f = f 42
f3 f = f 100

tw : {A : Set} → (A → A) → A → A
tw f n = f (f n)

-- consider

t : ℕ
t = (tw tw add3) 1

-- what is the type of this and why? ask Agda too (C-c C-d).
-- what is its value?  guess, and ask Agda too (C-c C-n).
{-
(tw  tw add3 ) 1 = tw def
(tw (tw add3)) 1 = tw def (külső)
(tw add3) (tw add3 1) = tw def (utolsó)
(tw add3) (add3 (add3 1)) = add3 def ×2 + ált. isk.
tw add3 7 = tw def
add3 (add3 7) = add3 def ×2 + ált. isk.
13
-}
-- Hány darab A → A típusú függvény létezik?

id' : {A : Set} → A → A
id' = λ z → z

-- Hány darab A → A → A típusú függvény létezik?



-- Alkalmazzuk n-szer a függvényt egy értékre.
recℕ : {A : Set} → (A → A) → A → ℕ → A
recℕ = {!!}