module 2021aut.t2.lib where

open import lib using (𝟚 ; tt ; ff)

--open import Agda.Builtin.Bool
--open import Agda.Builtin.List
--open import Agda.Builtin.Char
--open import Agda.Builtin.Nat using (Nat)

postulate String : Set
{-# BUILTIN STRING String #-}

primitive
  primStringAppend   : String → String → String

{-# COMPILE JS primStringAppend = function(x) { return function(y) { return x+y; }; } #-}

infixr 1 _+++_
_+++_ : String → String → String
x +++ y = primStringAppend x y

data _—⠀testing⠀for_values:_≡_ (message : String) {i}(A : Set i) (a : A) : A → Set where
  test : message —⠀testing⠀for A values: a ≡ a

{- example usage:
test1 : "x should be one" —⠀testing⠀for ℕ values: zh.x ≡ 1
test1 = test
-}

𝟚to𝕊 : 𝟚 → String
𝟚to𝕊 tt = "`tt`"
𝟚to𝕊 ff = "`ff`"
