module tut.gy01 where

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
-- C-c C-n   : Evaluate
-- C-c C-,   : Goal type and context
-- C-c C-.   : Goal type and context + inferred type of current expr
-- C-c C-SPC : Fill goal
-- C-c C-x = : Describe character at point
-- modules

---------------------------------------------------------
-- Bool
---------------------------------------------------------

b1 b2 b3 b4 b5 : Bool
b1 = true
b2 = false
b3 = if b1 then b2 else b2
b4 = if b3 then b1 else b2
b5 = if (if (if true then b2 else b1) then b1 else b1) then b2 else b3
-- = if (if b2 then b1 else b1) then b2 else b3
-- = if (if false then b1 else b1) then b2 else b3
-- = if b1 then b2 else b3
-- = if true then b2 else b3
-- = b2
-- = false

-- write as many terms of type Bool as you can!

-- how many different Bool-terms are there?

-- what is b3? what is b4? normalise!

-- Agda key combinations:
--   C-c C-n

---------------------------------------------------------
-- Functions
---------------------------------------------------------

-- unicode: λ, "information about character at a point"
-- λ = \lambda

-- spaces matter

id idy id1 id'' id''' : Bool → Bool
id = λ x → x
idy = λ y → y -- λ y → y = λ y → (λ x → x) y = λ x → x

-- id b2 = (λ x → x) b2 = x[x ↦ b2] = b2 = false

id1 = λ x → id x

id' = λ x → if x then x else x
-- at the whiteboard: derive typing for id'!

id'' = λ x → if true then x else false
id''' = λ x → if x then true else false

b6 : Bool
b6 = id true

-- do we have id = id'? normalise!
-- and id = id''?

-- If their normal forms are different, then they are different. Agda
-- decides equality of terms this way.

not : Bool → Bool
not = λ x → if x then false else true

testnot : Bool
testnot = not false

not' : Bool → Bool
not' = λ x → not (not (not x))

not'' : Bool → Bool
not'' = λ x → not (not (not (not (not x))))

not''' : Bool → Bool
not''' = λ x → not (not (not (not (not (not (not x))))))

-- Functions with multiple arguments / Currying :
--   "Bool -> Bool -> Bool" = "Bool -> (Bool -> Bool)"

and and' : Bool → Bool → Bool
and = λ x y → if x then y else false
and' = λ x y → if x then if y then true else false else false

-- all Bool → Bool functions up to behaviour:
TT TF FT FF : Bool → Bool
TT = λ x → if x then true  else true
TF = λ x → if x then true  else false
FT = λ x → if x then false else true
FF = λ x → if x then false else false

b7 : Bool
b7 = and true false

andtest and'test : Bool → Bool
andtest  = λ x → and  true x
and'test = λ x → and' true x

-- write as many different elements of Bool → Bool as possible!

-- ask them to write functions of the following type:
f : (Bool → Bool) → Bool
f = {!!}

-- "f id" is not equal to "f not"
-- => id does not have the same behaviour as not

-- Try to construct "g : (Bool -> Bool) -> Bool" such that
--   "g id = g T", "g not = g F" and "g id" is not equal to "g not"
g : (Bool → Bool) → Bool
g = {!!}

-- and then the following types
h : ((Bool → Bool) → Bool) → Bool
h = {!!}

i : (((Bool → Bool) → Bool) → Bool) → Bool
i = {!!}
