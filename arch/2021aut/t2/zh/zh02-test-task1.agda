module zh02-test-task1 where
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

test-1 : "task1₁ should be a boolean" —⠀testing 𝟚 typed zh02.task1₁ is zh02.task1₁
test-1 = test

test-2 : "task1₂ should be a boolean" —⠀testing 𝟚 typed zh02.task1₂ is zh02.task1₂
test-2 = test

test-3 : "task1₁ should differ from task1₂" —⠀testing 𝟚 typed (zh02.task1₁ xor zh02.task1₂) is tt
test-3 = test
