module zh02-test-bonus where
import zh02
open import lib

postulate String : Set
{-# BUILTIN STRING String #-}

data _—⠀testing_typed_is_ (message : String) {i}(A : Set i) (a : A) : A → Set where
  test : message —⠀testing A typed a is a

--test1 : "x should be one" —⠀testing ℕ typed zh01.x is 1
--test1 = test

not : 𝟚 → 𝟚
not a = if a then ff else tt

_xor_ : 𝟚 → 𝟚 → 𝟚
a xor b = if a
  then not b
  else b

test-1 : "bonus should equal to bonus'" —⠀testing 𝟚 typed zh02.bonus is zh02.bonus'
test-1 = test

test-2 : String
test-2 = "The line defining bonus' should be short - will be checked by hand"
