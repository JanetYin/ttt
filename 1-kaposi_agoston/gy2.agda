module gy2 where

open import lib

id : Bool → Bool
id = λ x → x

t1 : Bool
t1 = true

not : Bool → Bool
not = λ x → if x then false else true

TT TF FT FF : Bool → Bool
TT = λ x → true
TF = λ x → if x then true else false -- =? id?
--FT =
--FF =

TT' : Bool → Bool
TT' = λ x → if true then true else false 

-- evaluate with C-c C-n

-- The only functions of type "Bool -> Bool" up to behaviour are id, not, T and F
-- Try to construct "g : (Bool -> Bool) -> Bool" such that
--   "g id = g T", "g not = g F" and "g id" is not equal to "g not"

-- Functions with multiple arguments / Currying :
--   "Bool -> Bool -> Bool" = "Bool -> (Bool -> Bool)"

and or nand xor : Bool → Bool → Bool
-- and =
-- or =
-- nand =
-- xor =

-- Function as an argument
f : (Bool → Bool) → Bool
f = λ g → g false


---------------------------------------------------------
-- Natural numbers
---------------------------------------------------------

three = suc (suc (suc zero))

seventyseven : ℕ
seventyseven = 77

plus3 : ℕ → ℕ


-- test it!

times2 : ℕ → ℕ


-- test it!

-- prefix operator

_*3+2 : ℕ → ℕ


-- infix operator, fixity

infixl 4 _+_

_+_ : ℕ → ℕ → ℕ


-- test it e.g. (3 + 4) + 5 = 3 + (4 + 5)

-- requirements: isZero zero = true, otherwise: false
isZero : ℕ → Bool

-- requirements: pred 0 = 0, pred (1 + n) = n
pred : ℕ → ℕ


even : ℕ → Bool

odd  : ℕ → Bool


-- product of two natural numbers
_*_ : ℕ → ℕ → ℕ
_*_ = λ x y → primrec zero (λ _ n → y + n) x

-- exponentiation of natural numbers
_^_ : ℕ → ℕ → ℕ

-- subtraction
_-_ : ℕ → ℕ → ℕ

equal? : ℕ → ℕ → Bool

_≥?_ : ℕ → ℕ → Bool

_>?_ : ℕ → ℕ → Bool
