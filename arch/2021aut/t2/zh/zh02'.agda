module zh02'  where

----------------------------
--  Ignore the following  --
-- until "ZH starts here" --
----------------------------

open import Agda.Builtin.Bool renaming (Bool to 𝟚 ; false to ff ; true to tt)
open import Agda.Builtin.Equality
if_then_else_ : {A : Set} → 𝟚 → A → A → A
if tt then x else y = x
if ff then x else y = y

--------------------
-- ZH starts here --
--------------------

-- Task 1: Construct two 𝟚-terms with same semantics but different syntactics
-- In other words: They have to be equal (`C-c C-n task1₁` and `C-c C-n task1₂` should output the same), but defined in a different way (the list of words (separated by space) after the _=_ sign have to differ in contents)
task1₁ task1₂ : 𝟚
task1₁ = ?
task1₂ = ?
-- Note: This is the opposite of zh02.task1
-- If solved correctly, the following should be fine:
task1-test : task1₁ ≡ task1₂
task1-test = refl

-- Task 2: Replace the question mark with a lambda-sign and uncomment the following
{-
task2 : 𝟚 → 𝟚
task2 = ? x → x
-}

