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
times2 = λ n → primrec zero (λ _ fn' → suc (suc fn')) n

-- test it!

-- prefix operator

_*3+2 : ℕ → ℕ
_*3+2 = λ n → primrec (suc (suc zero)) (λ _ fn' → suc (suc (suc fn'))) n

-- infix operator, fixity

infixl 4 _+_

_+_ : ℕ → ℕ → ℕ
_+_ = λ x y → primrec x (λ _ fy' → suc fy') y


-- test it e.g. (3 + 4) + 5 = 3 + (4 + 5)

-- requirements: isZero zero = true, otherwise: false
isZero : ℕ → Bool
isZero = λ n → primrec true (λ _ _ → false) n

-- requirements: pred 0 = 0, pred (1 + n) = n
pred : ℕ → ℕ
pred = λ n → primrec zero (λ n' fn' → n') n


even : ℕ → Bool
even = λ n → primrec true (λ _ fn' → not fn') n


odd  : ℕ → Bool
--HW.

-- sum of the natural numbers from 0 to n.
-- requirements: sum(0) = 0, sum(1) = 1, sum(2) = 3, sum(3) = 6, sum(4) = 10, ...
sum : ℕ → ℕ
-- HW.

-- product of two natural numbers
_*_ : ℕ → ℕ → ℕ
_*_ = {!!}
-- HW. based on _+_ which we solved together on the class

-- exponentiation of natural numbers
_^_ : ℕ → ℕ → ℕ
_^_ = {!!}

-- subtraction
_-_ : ℕ → ℕ → ℕ
_-_ = {!!}

equal? : ℕ → ℕ → Bool
equal? = {!!}

_≥?_ : ℕ → ℕ → Bool
_≥?_ = {!!}

_>?_ : ℕ → ℕ → Bool
_>?_ = {!!}
