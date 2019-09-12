module gy1 where

open import lib

b1 : Bool
b1 = true
b2 : Bool
b2 = false
b3 : Bool
b3 = if false then false else true
b4 : Bool
b4 = if (if b2 then b1 else true) then b3 else b2
-- = if (if false then b1 else true) then b3 else b2
-- = if true then b3 else b2
-- = b3
-- = if false then false else true
-- = true

id id' id'' id1 : Bool → Bool
id = λ x → x
id' = λ x → if x then true else false
id'' = λ x → id x
id1 = λ x → if true then x else false

TT TF FT FF : Bool → Bool
TT = λ x → true
TF = λ x → x
FT = λ x → if x then false else true
FF = λ x → false

TT' TF' FT' FF' TT'' : Bool → Bool
TT' = λ x → if x then true  else true
TF' = λ x → if x then true  else false
FT' = λ x → if x then false else true
FF' = λ x → if x then false else false

TT'' = λ x → if x then (if x then true else false) else true
