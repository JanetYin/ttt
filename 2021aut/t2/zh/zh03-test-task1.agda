module 2021aut.t2.zh.zh03-test-task1 where

--open import Agda.Builtin.String using () renaming (primStringAppend to _+_)
open import lib
open import 2021aut.t2.lib
--import 2021aut.t2.zh.zh03 as zh
import zh03 as zh

TestCase : 𝟚 → 𝟚 → 𝟚 → Set
TestCase x y result = message —⠀testing⠀for 𝟚 values: zh.task1 x y ≡ result
  where
    message : String
    message = "Testing for " +++ 𝟚to𝕊 x +++ " OR " +++ 𝟚to𝕊 y +++ " (= " +++ 𝟚to𝕊 result +++ ")"

test1 : TestCase ff ff ff
test1 = test

test2 : TestCase ff tt tt
test2 = test

test3 : TestCase tt ff tt
test3 = test

test4 : TestCase tt tt tt
test4 = test
