module gy01 where

open import lib

-- 1. git clone
--       https://bitbucket.org/akaposi/ttt
-- 2. Alt+F2 "emacs"
-- 3. Create a file "ttt/tut1.agda"
-- 4. Typecheck with "C-c C-l"
--      -> the file should be colored

-- Emacs key bindings (C = Ctrl, M = Alt):
-- C-x C-f : create or open a file
-- C-x C-w : save (write) file
-- C-x C-c : close Emacs
-- C-space : start selecting text
-- M-w : Copy
-- C-w : Cut
-- C-y : Paste
--
-- Agda-mode key bindings:
-- C-c C-l   : Typecheck
-- C-c C-n   : Evaluate (normalise)
-- C-c C-,   : Goal type and context
-- C-c C-.   : Goal type and context + inferred type of current expr
-- C-c C-SPC : Fill goal
-- C-c C-x = : Describe character at point
-- C-u C-u C-c C-, : Normalise goal
-- modules

---------------------------------------------------------
-- Booleans
---------------------------------------------------------

b1 b2 b3 b4 b5 : 𝟚
b1 = tt
b2 = ff
b3 = if b1 then b2 else b2
b4 = if b3 then b1 else b2
b5 = if (if (if tt then b2 else b1) then b1 else b1) then b2 else b3
-- = if (if b2 then b1 else b1) then b2 else b3
-- = if (if ff then b1 else b1) then b2 else b3
-- = if b1 then b2 else b3
-- = if tt then b2 else b3
-- = b2
-- = ff

-- write as many terms of type 𝟚 as you can!

-- how many different 𝟚-terms are there?

-- what is b3? what is b4? normalise!

-- Agda key combinations:
--   C-c C-n

---------------------------------------------------------
-- Functions
---------------------------------------------------------

-- unicode: λ, Agda menu / "Information about the character at point"
-- λ = \lambda

-- spaces matter

id idy id1 id'' id''' : 𝟚 → 𝟚
id = λ x → x
idy = λ y → y -- λ y → y = λ y → (λ x → x) y = λ x → x

-- id b2 = (λ x → x) b2 = x[x ↦ b2] = b2 = ff

id1 = λ x → id x

id' = λ x → if x then x else x
-- at the whiteboard: derive typing for id'!

id'' = λ x → if tt then x else ff
id''' = λ x → if x then tt else ff

b6 : 𝟚
b6 = id tt

-- do we have id = id'? normalise!
-- and id = id''?

-- If their normal forms are different, then they are different. Agda
-- decides equality of terms this way.

not : 𝟚 → 𝟚
not = λ x → if x then ff else tt

testnot : 𝟚
testnot = not ff

not' : 𝟚 → 𝟚
not' = λ x → not (not (not x))

not'' : 𝟚 → 𝟚
not'' = λ x → not (not (not (not (not x))))

not''' : 𝟚 → 𝟚
not''' = λ x → not (not (not (not (not (not (not x))))))

-- Functions with multiple arguments / Currying :
--   "𝟚 -> 𝟚 -> 𝟚" = "𝟚 -> (𝟚 -> 𝟚)"

and and' : 𝟚 → 𝟚 → 𝟚
and = λ x y → if x then y else ff
and' = λ x y → if x then if y then tt else ff else ff

-- all 𝟚 → 𝟚 functions up to behaviour:
TT TF FT FF : 𝟚 → 𝟚
TT = λ x → if x then tt  else tt
TF = λ x → if x then tt  else ff
FT = λ x → if x then ff else tt
FF = λ x → if x then ff else ff

b7 : 𝟚
b7 = and tt ff

andtest and'test : 𝟚 → 𝟚
andtest  = λ x → and  tt x
and'test = λ x → and' tt x

-- write as many different elements of 𝟚 → 𝟚 as possible!

-- write functions of the following type:
f : (𝟚 → 𝟚) → 𝟚
f = {!!}

-- "f id" is not equal to "f not"
-- => id does not have the same behaviour as not

-- Try to construct "g : (𝟚 -> 𝟚) -> 𝟚" such that
--   "g id = g T", "g not = g F" and "g id" is not equal to "g not"
g : (𝟚 → 𝟚) → 𝟚
g = {!!}

-- define as many different functions of this type as possible!
h : ((𝟚 → 𝟚) → 𝟚) → 𝟚
h = {!!}

i : (((𝟚 → 𝟚) → 𝟚) → 𝟚) → 𝟚
i = {!!}
