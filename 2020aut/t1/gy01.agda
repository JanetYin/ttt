module tut.t1.gy01 where

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
-- C-c C-l : Typecheck
-- C-c C-n : Evaluate
-- C-c C-, : Goal type and context
-- C-x C-. : Goal type and context + inferred type of given expressiom
-- C-c C-SPC : Fill hole

-- M-x describe-char - check how to input character



---------------------------------------------------------
-- Bool
---------------------------------------------------------
{-
introduction:
  true : Bool
  false : Bool

elimination:
  if   t : Bool, u v : A
  then if t then u else v : A
  for any type A

computation:
  if true then u else v = u
  if false then u else v = v
-}

b1 b2 b3 b4 b5 : Bool
b1 = true
b2 = false
b3 = if b1 then b2 else b2
b4 = if b3 then b1 else b2
b5 = if (if (if true then b2 else b1) then b1 else b1) then b2 else b3
-- = if (if b2 then b1 else b1) then b2 else b3
-- = if (if false then b1 else b1) then b2 else b3
-- = if b1 then b2 else b3
-- = if true then
-- b2 else b3
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

{-
if A and B are types, then so is A → B 

introduction
  if   t : B, assuming  x : A
  then (λ x → t) : A → B

elimination:
  if   t : A → B, u : A
  then t u : B.

computation:
  (λ x → t) u = t [x → u]

uniqueness:
  (λ x → t x) = t

-}

-- unicode: λ
-- λ = \lambda = \Gl \-> = →

-- spaces matter

id idy id1 id'' id''' : Bool → Bool
id = λ x → x
idy = λ y → y 

-- id = λ x → x = λ x → (λ y → y) x = λ y → y

-- id b2 = (λ x → x) b2 = x[x ↦ b2] = b2 = false

id1 = λ x → id x

-- id = id1
-- function extensionality: ∀x (f x = g x) → f = g
-- we don't have this in our theory!
-- in set theory, where everything is a set, we have extensionality
-- (see : axiom of extensionality)

id' : Bool → Bool
id' = λ x → if x then x else x
-- at the whiteboard: derive typing for id'!

id'' = λ x → if true then x else false
id''' = λ x → if x then true else false

b6 : Bool
b6 = id true

-- do we have id = id'? normalise!
-- and id = id''?

-- If their normal forms are different, then they are different. Agda
-- decides equality of terms this way (definitional equality)

-- we can't write a term that behaves like this:
-- f x = if x = t (def), then u else v
-- definitional equality is a judgement (like x : A), not a proposition

-- can we write
-- t : Bool
-- such that
-- t ≠ true, t ≠ false (def)

-- f : Bool → Bool, f = λ x → t
-- f b = (λ x → t) b = t [x → b] 

not : Bool → Bool
not = λ x → if x then false else true

-- not true = λ x → (if x then false else true) true = (if true then false else true) = false 

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
f = λ x → x true 
-- x : Bool → Bool
-- true : Bool
-- x true Bool


-- "f id" is not equal to "f not"
-- => id does not have the same behaviour as not

-- Try to construct "g : (Bool -> Bool) -> Bool" such that
--   "g id = g T", "g not = g F" and "g id" is not equal to "g not"
g : (Bool → Bool) → Bool
g = λ f → f true

-- and then the following types
h : ((Bool → Bool) → Bool) → Bool
h = {!!}

i : (((Bool → Bool) → Bool) → Bool) → Bool
i = {!!}
  
