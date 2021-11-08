module zh03'-task2 where

open import lib

-- Some predefined functions, you can use them:
id : 𝟚 → 𝟚
id x = x

not : 𝟚 → 𝟚
not x = if x then ff else tt

and : 𝟚 → 𝟚 → 𝟚
and x y = if x then y else ff


-- There are no bonus points.

-- Task 2: Define the NAND operation, which is a logical operation on two logical values. It produces a value of `tt`, if — and only if — at least one of the propositions is `ff`.

task2 : 𝟚 → 𝟚 → 𝟚
task2 = ?

{-
The truth table of 𝑃↑𝑄 (also written as 𝑃|𝑄, or D𝑝𝑞) is as follows

𝑃 𝑄 𝑃↑𝑄
T T  F
T F  T
F T  T
F F  T
-}

-- Source: Wikipedia
