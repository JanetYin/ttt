module zh01-test where

import zh01
open import lib

postulate String : Set
{-# BUILTIN STRING String #-}

data _—⠀testing_typed_is_ (message : String) {i}(A : Set i) (a : A) : A → Set where
  test : message —⠀testing A typed a is a

test1 : "x should be one" —⠀testing ℕ typed zh01.x is 1
test1 = test
