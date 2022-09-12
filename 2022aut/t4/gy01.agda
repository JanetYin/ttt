open import Agda.Builtin.Nat
  using (zero; suc; _+_; _*_)
  renaming (Nat to ℕ)

--

-- 1. git clone https://bitbucket.org/akaposi/ttt
-- 2. Open this file (2022aut/t4/gy01.agda) in emacs. (On the lab computers: Alt-F2 "emacs")
-- 3. Typecheck with "C-c C-l"
--      -> the file should now be colored

-- Emacs key bindings (C = Ctrl, M = Alt):
--  C-x C-f : create or open a file
--  C-x C-w : save (write) file
--  C-x C-c : close Emacs
--  C-space : start selecting text
--  M-w : Copy
--  C-w : Cut
--  C-y : Paste

-- Agda-mode key bindings:
--  C-\       : Switch Agda input mode on/off
--  C-c C-l   : Typecheck the current file
--  C-c C-n   : Normalise an expression (reduce the expression as much as possible)
--  C-c C-d   : Deduce the type of an expression
--  C-c C-,   : Show the goal type and context of a hole
--                (C-u C-u C-c C-, : same but fully normalise the goal
--                 C-u C-c C-,     : same but do not normalise the goal)
--  C-c C-.   : Goal type and context + inferred type of current expression
--  C-c C-SPC : Fill goal
--  C-c C-x = : Describe character at point

-- add3

add3 : ℕ → ℕ -- \bN \to \bN
add3 x = x + 3

-- try add3 x = x+3, spaces matter!

-- C-c C-n  add3 4

aNum : ℕ
aNum = add3 4

-- no need to write brackets as in "add3(4)"

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
add4 x = {!!}

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

--- Higher-order functions
-- write a function of the following type:

f1 : (ℕ → ℕ) → ℕ
f1 = {!!}

-- test it with f1 add3, f1 add4. is the result the same?

-- write two different functions which use their inputs, i.e. f2 add3 ≠ f2 add4 ≠ f3 add4 ≠ f3 add3

f2 f3 : (ℕ → ℕ) → ℕ
f2 = {!!}
f3 = {!!}

-- Polymorphic functions

-- {A : Set} is an implicit argument
id : {A : Set} → A → A
id x = x

idℕ : ℕ → ℕ
idℕ = id {ℕ}

three : ℕ
three = idℕ 3

three' : ℕ
three' = id 3 {- The implicit argument A is inferred and solved with  A = ℕ  -}

const : {A B : Set} → A → B → A
const = {!!}

-- Define function composition
-- \circ
_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
_∘_ = {!!}
infixl 5 _∘_ -- (f ∘ g ∘ h) = ((f ∘ g) ∘ h)

-- How can you test your definition of _∘_ ?

-- write a function twice that applies the given function twice.
twice : {A : Set} → (A → A) → A → A
twice = {!!}

-- what is the result of  twice add3 1 ?
-- what about             twice twice add3 1 ?
