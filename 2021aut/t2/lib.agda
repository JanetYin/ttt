module 2021aut.t2.lib where

postulate String : Set
{-# BUILTIN STRING String #-}

data _—⠀testing⠀for_values:_≡_ (message : String) {i}(A : Set i) (a : A) : A → Set where
  test : message —⠀testing⠀for A values: a ≡ a

{- example usage:
test1 : "x should be one" —⠀testing⠀for ℕ values: zh01.x ≡ 1
test1 = test
-}
