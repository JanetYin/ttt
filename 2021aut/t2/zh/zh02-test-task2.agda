module zh02-test-task2 where
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

test-1 : "task2 should be the type 𝟚" —⠀testing Set typed zh02.task2 is 𝟚
test-1 = test
