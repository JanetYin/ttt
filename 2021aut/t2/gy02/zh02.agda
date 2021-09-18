{-# OPTIONS --allow-unsolved-metas #-}
module zh02 where
open import lib

-- Task 1: Construct two different 𝟚 values.
task1₁ task1₂ : 𝟚
task1₁ = tt -- C-c C-a
task1₂ = ff

-- Task 2: Which type does `tt` have?
task2 : Set
task2 = 𝟚 -- \b2
-- If task2 is defined, the following should be fine:
task2' : task2
task2' = tt

-- Bonus: Check the following:
bonus : 𝟚
bonus = if (if (if (if (if (if tt then ff else tt) then ff else tt) then (if (if ff then ff else tt) then ff else tt) else tt) then tt else ff) then ff else ff) then tt else ff
-- Now normalize `task3` (without backticks). How can we write it simplier?
bonus' : 𝟚
bonus' = ff -- C-c C-n bonus ENTER
-- (the above line should be no longer than 10 characters)
