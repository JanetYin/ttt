open import Agda.Builtin.Nat renaming (Nat to ℕ)

-- 1. git clone https://bitbucket.org/akaposi/ttt
-- 2. Alt+F2 "emacs"
-- 3. Create a file "ttt/tut1.agda"
-- 4. Typecheck with "C-c C-l"
--      -> the file should be colored


-- Emacs key bindings (C = Ctrl, M = Alt):
-- C-x C-f : create or open a file
-- C-x C-s : save
-- C-x C-w : save as
-- C-x C-c : close Emacs
-- C-space : start selecting text
-- M-w : Copy
-- C-w : Cut
-- C-y : Paste
-- C-x u : Undo

-- Agda-mode key bindings:
-- C-\       : Switch Agda mode on-off (a speciális karakteresdi ki- és bekapcsolása)
-- C-c C-l   : Typecheck
-- C-c C-n   : Normalise (use definitions as much as possible) (kiértékelés)
-- C-c C-d   : Deduce type (típus)
-- modules

-- Unicode characters:
-- ℕ is \bN, ℤ is \bZ etc.
-- → is \r →
-- α is \Ga, β is \Gb etc.

-- C-c C-,   : Goal type and context (variants: C-u C-u C-c C-, and C-u C-c C-, where you normalise or do not normalise the goal at all)
-- C-c C-.   : Goal type and context + inferred type of current expr
-- C-c C-SPC : Fill goal
-- C-c C-x = : Describe character at point

add3 : ℕ → ℕ -- \bN \r \bN
add3 x = x + 3

e1e⟨e⟩3 : ℕ -- furák is lehetnek az identifierek (cserébe szóközökre háklis)
e1e⟨e⟩3 = 6

nat : ℕ
nat = add3 4  --? is a hole (write a ? and press C-c C-l after this)

-- God gives as _+_ and 

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
-- λ is \Gl ("Greek 'l'")

add3' : ℕ → ℕ
add3' = λ x → x + 3

-- test it with C-c C-n!

-- az első óra vége
------------------------------------------

-- kis ismétlés:
add4 : ℕ → ℕ
add4 = λ x → x + 4

-- functions with multiple arguments

add : ℕ → (ℕ → ℕ)           -- ugyanaz, mint ℕ → ℕ → ℕ (lásd hf.)
add = λ x → (λ y → x + y)

-- add 3 4
{-
add 3
(λ x → (λ y → x + y)) 3   = (λ y → 3 + y) 
-}

-- bracketing of λ

-- same as λ x → λ y → x + y
-- same as λ x y → x + y

-- lehet így is:
add' : ℕ → ℕ → ℕ
add' x y = x + y

-- de így is:
add'' : ℕ → ℕ → ℕ
add'' = _+_              -- (+) in Haskell

num1 : ℕ
num1 = add 3 4

-- bracketing of application

num1' : ℕ
num1' = (add 3) 4           -- try C-c C-d with add 3

-- what is wrong with the following?

a b : ℕ
a = 3
b = 4

{-
num2 : ℕ
num2 = add (a b)

(a    b)
 |    |
 ℕ   ℕ
-}

-- ℕ → (ℕ → ℕ)   ≡ ℕ → ℕ → ℕ

{-
num3 : ℕ
num3 = add 3 (add 4)
-}

num4 : ℕ
num4 = add 3 (add 4 2)

-- write a function of the following type:

-- C-c C-g  - quit

f1 : (ℕ → ℕ) → ℕ   -- itt már kell a zárójel
--f1 f = f 5
f1 = λ f → f 5

-- test it with f1 add3, f1 add4. is the result the same?

-- write 

f2 : (ℕ → ℕ) → ℕ
f2 f = {!f (f 5)!}
