{-# OPTIONS --allow-unsolved-metas #-}
module zh01 where
open import lib

x : ℕ
-- x should be one. Lets replace the hole with the number 1!
-- Steps:
--   1. Load the file:  C-c C-l
--   2. Go to the hole: C-c C-f
--   3. Try to refine:  C-c C-r
--   4. :(
--   5. Enter "1"
--   6. Now "save" the value: C-c C-SPC
x = {!1!}

{-
-- Example solution:
x : ℕ
x = 1
-}
