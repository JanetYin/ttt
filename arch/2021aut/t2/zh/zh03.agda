module zh03 where

open import lib

-- Some predefined functions, you can use them:
id : 𝟚 → 𝟚
id x = x

not : 𝟚 → 𝟚
not x = if x then ff else tt

and : 𝟚 → 𝟚 → 𝟚
and x y = if x then y else ff


-- Bonus 1: For bonus points, don't use the functions `tt` and `ff`, but use the given functions above and / or the input parameters

-- Bonus 2: For even more bonus points, return with `id` or `not` at least once
--          (but don't modify them)

-- Task 1: Define the logical `or` function, which should be `tt` if and only if either of the parameters are `tt`
or : 𝟚 → 𝟚 → 𝟚
--or = λ x y  →  if x then x else y
or x y = if x then x else y

{- Here is the OR table for reference:

       |       |       |
 OR    | true  | false |
       |       |       |
-------+-------+-------+
       |       |       |
 true  | true  | true  |
       |       |       |
-------+-------+-------+
       |       |       |
 false | true  | false |
       |       |       |
-------+-------+-------+

-}

task1 = or

-- Task 2: Define the logical `xor` funcion, which should be `ff` if and only if it's parameters are equal
xor : 𝟚 → 𝟚 → 𝟚
xor = λ x → if x then not else id
--xor = {!!}

{- Here is the XOR table for reference:

       |       |       |
 XOR   | true  | false |
       |       |       |
-------+-------+-------+
       |       |       |
 true  | false | true  |
       |       |       |
-------+-------+-------+
       |       |       |
 false | true  | false |
       |       |       |
-------+-------+-------+

-}

task2 = xor
