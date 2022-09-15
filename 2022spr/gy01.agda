open import Agda.Builtin.Nat renaming (Nat to ℕ)

-- 1. git clone https://bitbucket.org/akaposi/ttt
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
-- C-\       : Switch Agda mode on-off
-- C-c C-l   : Typecheck
-- C-c C-n   : Normalise (use definitions as much as possible)
-- C-c C-d   : Deduce type
-- C-c C-,   : Goal type and context (variants: C-u C-u C-c C-, and C-u C-c C-, where you normalise or do not normalise the goal at all)
-- C-c C-.   : Goal type and context + inferred type of current expr
-- C-c C-SPC : Fill goal
-- C-c C-x = : Describe character at point
-- modules

-- God gives as _+_ and 

add3 : ℕ → ℕ -- \N \ra \N
add3 x = x + 3

-- try add3 x = x+3, spaces matter!

-- C-c C-n  add3 4

aNum : ℕ
aNum = add3 4

-- no need to write brackets in "add3(4)"

-- C-c C-n aNum

bNum : ℕ
bNum = add3 (add3 (add3 2))

-- "add3 add3 add3 2" is wrong

-- C-c C-n bNum

-- lambda notation

add3' : ℕ → ℕ
add3' = λ x → x + 3

-- test it with C-c C-n!

add4 : ℕ → ℕ
add4 = {!!}

-- functions with multiple arguments

add : ℕ → (ℕ → ℕ)
add = λ x → (λ y → x + y)

-- bracketing of λ

-- same as λ x → λ y → x + y
-- same as λ x y → x + y

num1 : ℕ
num1 = add 3 4

-- bracketing of application

num1' : ℕ
num1' = (add 3) 4

-- what is wrong with the following?

-- num2 : ℕ
-- num2 = add (3 4)

-- num3 : ℕ
-- num3 = add 3 (add 4)

num4 : ℕ
num4 = add 3 (add 4 2)

-- write a function of the following type:

f1 : (ℕ → ℕ) → ℕ
f1 = {!!}

-- test it with f1 add3, f1 add4. is the result the same?

-- write two different functions which use their inputs, i.e. f2 add3 ≠ f2 add4 ≠ f3 add4 ≠ f3 add3

f2 f3 : (ℕ → ℕ) → ℕ
f2 = {!!}
f3 = {!!}


