module gy1 where

open import lib

b1 b2 b3 b4 : Bool
b1 = true
b2 = false
b3 = if true then false else true
b4 = if (if (if true then b2 else b1) then b1 else b1) then b2 else b3
--   if (if b2 then b1 else b1) then b2 else b3
--   if (if false then b1 else b1) then b2 else b3
--   if b1 then b2 else b3
--   if true then b2 else b3
--   b2
--   false

id : Bool → Bool
id = λ x → x
-- id b2 = (λ x → x) b2 = x[x ↦ b2] = b2 = false
idy : Bool → Bool
idy = λ alma → alma

id' : Bool → Bool
id' = λ x → if x then true else false

id'' = λ x → if true then x else false -- = λ x → x

id''' : Bool → Bool
id''' = λ x → if (if x then true else false) then true else false
-- ...

-- not, and, or, xor

not : Bool → Bool
not = λ x → if x then false else true

not' : Bool → Bool
not' = λ x → not (not (not x))

not'' : Bool → Bool
not'' = λ x → not (not (not (not (not x))))

not''' : Bool → Bool
not''' = λ x → not (not (not (not (not (not (not x))))))

TT TF FT FF : Bool → Bool
TT = λ x → if x then true  else true
TF = λ x → if x then true  else false
FT = λ x → if x then false else true
FF = λ x → if x then false else false

and : Bool → Bool → Bool
and = λ x y → if x then y else false
--          ^ ha x : Bool, akkor ... : Bool → Bool
-- aaa : Bool, felteve, hogy x : Bool es y : Bool

-- or, xor

xor : Bool → Bool → Bool
xor = λ x y → if x then not y else y

-- f : Bool
-- f = f

f : (Bool → Bool) → Bool
f = λ w → w true

h : ((Bool → Bool) → Bool) → Bool
i : (((Bool → Bool) → Bool) → Bool) → Bool
