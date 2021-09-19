{-# OPTIONS --allow-unsolved-metas #-} -- unresolved metas ≈ empty holes

module 2021aut.t2.gy02.exercise where

open import lib
open import 2021aut.t2.lib

-- not is the logical negation - should return ff for tt and tt for ff
not : 𝟚 → 𝟚
not = λ a → if a then ff else tt

-- Test: you don't have to modify these, but you'll get an error if you do something wrong.
-- Feel free to comment them out if needed.
test-not-1 : "not ff" —⠀testing⠀for 𝟚 values: not ff ≡ tt
test-not-1 = test
test-not-2 : "not tt" —⠀testing⠀for 𝟚 values: not tt ≡ ff
test-not-2 = test

-- id is the opposite - it passes the value as-is
id : 𝟚 → 𝟚
id = λ a → if a then tt else ff
-- or shorter:
id, : 𝟚 → 𝟚
id, = λ a → a

test-id-1 : "id ff" —⠀testing⠀for 𝟚 values: id ff ≡ ff
test-id-1 = test
test-id-2 : "id tt" —⠀testing⠀for 𝟚 values: id tt ≡ tt
test-id-2 = test
test-id,-1 : "id, ff" —⠀testing⠀for 𝟚 values: id, ff ≡ ff
test-id,-1 = test
test-id,-2 : "id, tt" —⠀testing⠀for 𝟚 values: id, tt ≡ tt
test-id,-2 = test

-- logical and - a little more complicated, but still straightforward
and : 𝟚 → 𝟚 → 𝟚
and = λ a b → if a then (if b then tt else ff) else (if b then ff else ff)
-- here it is broken up to multiple lines:
and, : 𝟚 → 𝟚 → 𝟚
and, = λ a b →
  if a
  then (
    if b
    then ff
    else tt
 ) else ff

test-and-1 : "and ff ff = ff" —⠀testing⠀for 𝟚 values: and ff ff ≡ ff
test-and-1 = test
test-and-2 : "and ff tt = ff" —⠀testing⠀for 𝟚 values: and ff tt ≡ ff
test-and-2 = test
test-and-3 : "and tt ff = ff" —⠀testing⠀for 𝟚 values: and tt ff ≡ ff
test-and-3 = test
test-and-4 : "and tt tt = tt" —⠀testing⠀for 𝟚 values: and tt tt ≡ tt
test-and-4 = test

-- logical or - try it yourself
or : 𝟚 → 𝟚 → 𝟚
or = {!!}

test-or-1 : "or ff ff = ff" —⠀testing⠀for 𝟚 values: or ff ff ≡ ff
test-or-1 = test
test-or-2 : "or ff tt = ff" —⠀testing⠀for 𝟚 values: or ff tt ≡ tt
test-or-2 = test
test-or-3 : "or tt ff = ff" —⠀testing⠀for 𝟚 values: or tt ff ≡ tt
test-or-3 = test
test-or-4 : "or tt tt = tt" —⠀testing⠀for 𝟚 values: or tt tt ≡ tt
test-or-4 = test

-- let's practice a little more on xor
xor : 𝟚 → 𝟚 → 𝟚
xor = {!!}

test-xor-1 : "xor ff ff = ff" —⠀testing⠀for 𝟚 values: xor ff ff ≡ ff
test-xor-1 = test
test-xor-2 : "xor ff tt = ff" —⠀testing⠀for 𝟚 values: xor ff tt ≡ tt
test-xor-2 = test
test-xor-3 : "xor tt ff = ff" —⠀testing⠀for 𝟚 values: xor tt ff ≡ tt
test-xor-3 = test
test-xor-4 : "xor tt tt = tt" —⠀testing⠀for 𝟚 values: xor tt tt ≡ tt
test-xor-4 = test

-- Now try a different approach: You can also return the arguments as-is, as seen in id,
and' : 𝟚 → 𝟚 → 𝟚
and' = λ a b → if a then b else ff

test-and'-1 : "and' ff ff = ff" —⠀testing⠀for 𝟚 values: and' ff ff ≡ ff
test-and'-1 = test
test-and'-2 : "and' ff tt = ff" —⠀testing⠀for 𝟚 values: and' ff tt ≡ ff
test-and'-2 = test
test-and'-3 : "and' tt ff = ff" —⠀testing⠀for 𝟚 values: and' tt ff ≡ ff
test-and'-3 = test
test-and'-4 : "and' tt tt = tt" —⠀testing⠀for 𝟚 values: and' tt tt ≡ tt
test-and'-4 = test

-- or should be similar
or' : 𝟚 → 𝟚 → 𝟚
or' = {!!}

test-or'-1 : "or' ff ff = ff" —⠀testing⠀for 𝟚 values: or' ff ff ≡ ff
test-or'-1 = test
test-or'-2 : "or' ff tt = ff" —⠀testing⠀for 𝟚 values: or' ff tt ≡ tt
test-or'-2 = test
test-or'-3 : "or' tt ff = ff" —⠀testing⠀for 𝟚 values: or' tt ff ≡ tt
test-or'-3 = test
test-or'-4 : "or' tt tt = tt" —⠀testing⠀for 𝟚 values: or' tt tt ≡ tt
test-or'-4 = test

-- You can also return expressions like `not b`
xor' : 𝟚 → 𝟚 → 𝟚
xor' = {!!}

test-xor'-1 : "xor' ff ff = ff" —⠀testing⠀for 𝟚 values: xor' ff ff ≡ ff
test-xor'-1 = test
test-xor'-2 : "xor' ff tt = ff" —⠀testing⠀for 𝟚 values: xor' ff tt ≡ tt
test-xor'-2 = test
test-xor'-3 : "xor' tt ff = ff" —⠀testing⠀for 𝟚 values: xor' tt ff ≡ tt
test-xor'-3 = test
test-xor'-4 : "xor' tt tt = tt" —⠀testing⠀for 𝟚 values: xor' tt tt ≡ tt
test-xor'-4 = test

-- Advanced: Function currying works here too
and'' : 𝟚 → 𝟚 → 𝟚
and'' = λ a → if a then id else λ _ → ff

test-and''-1 : "and'' ff ff = ff" —⠀testing⠀for 𝟚 values: and'' ff ff ≡ ff
test-and''-1 = test
test-and''-2 : "and'' ff tt = ff" —⠀testing⠀for 𝟚 values: and'' ff tt ≡ ff
test-and''-2 = test
test-and''-3 : "and'' tt ff = ff" —⠀testing⠀for 𝟚 values: and'' tt ff ≡ ff
test-and''-3 = test
test-and''-4 : "and'' tt tt = tt" —⠀testing⠀for 𝟚 values: and'' tt tt ≡ tt
test-and''-4 = test

-- Try it yourself
or'' : 𝟚 → 𝟚 → 𝟚
or'' = {!!}

test-or''-1 : "or'' ff ff = ff" —⠀testing⠀for 𝟚 values: or'' ff ff ≡ ff
test-or''-1 = test
test-or''-2 : "or'' ff tt = ff" —⠀testing⠀for 𝟚 values: or'' ff tt ≡ tt
test-or''-2 = test
test-or''-3 : "or'' tt ff = ff" —⠀testing⠀for 𝟚 values: or'' tt ff ≡ tt
test-or''-3 = test
test-or''-4 : "or'' tt tt = tt" —⠀testing⠀for 𝟚 values: or'' tt tt ≡ tt
test-or''-4 = test

-- Now you have to return either `id` or `not`
xor'' : 𝟚 → 𝟚 → 𝟚
xor'' = {!!}

test-xor''-1 : "xor'' ff ff = ff" —⠀testing⠀for 𝟚 values: xor'' ff ff ≡ ff
test-xor''-1 = test
test-xor''-2 : "xor'' ff tt = ff" —⠀testing⠀for 𝟚 values: xor'' ff tt ≡ tt
test-xor''-2 = test
test-xor''-3 : "xor'' tt ff = ff" —⠀testing⠀for 𝟚 values: xor'' tt ff ≡ tt
test-xor''-3 = test
test-xor''-4 : "xor'' tt tt = tt" —⠀testing⠀for 𝟚 values: xor'' tt tt ≡ tt
test-xor''-4 = test

-- Some more ideas for individual practice:
-- nand
-- nor
-- eq
-- and3 : 𝟚 → 𝟚 → 𝟚
-- ...
