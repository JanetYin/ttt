module gy00 where

fun : {A : Set} → A → A
fun = λ a → a

data Bool : Set where
    true  : Bool
    false : Bool

record tt : Set where
    field
        b : Bool

-- open import Lib
{-
 open : A konetxtusban szeretnék rá teljes név nélkül hicatkozni
 import: Használni akarom a következő modult
-}

f : Int → Int
f = ?

