open import Lib.Containers.Stream.Type
open import Lib.Containers.List.Type
open import Lib.Nat

{-
Koindukció


Volt az indukció
- mintaillesztettünk a bemeneti paraméterekre

Koindukció
- comintaillesztünk az eredményre
comintaillesztés = eredmény részekre való felbontása

pl tuplere való comintaillesztés fst, snd


record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A

record típusoknak az a lényege hogy csak 1 konstruktoruk van

=> Stream végtelen hosszú
ezért kell a --guardedness

ún "proj"-kat lehet kiértékelni az egész streamet nem

-}

-- Stream amibe 0-k vannak
zeroes : Stream ℕ
head zeroes = 0
tail zeroes = zeroes

from : ℕ → Stream ℕ
head (from n) = n
tail (from n) = from (suc n) -- koindukciós hipotézis, elég awkward de na
{-
képzeljük el mint ha az első elemet levágnánk, mi marad? konkrét eset pl tök jó
-}


-- összecipzározza listát
zipWith : {A B C : Set} → (A → B → C) → Stream A → Stream B → Stream C
head (zipWith f sA sB) = f (head sA) (head sB)
tail (zipWith f sA sB) = zipWith f (tail sA) (tail sB)
{-

pl
[a,b,c,d,e,...]
[1,2,3,4,5,...]

|
V
[f a 1, f b 2, f c 3, f d 4, f e 5, ...]
|
snip snip (head megvolt)
V
[f b 2, f c 3, f d 4, f e 5, ...]
-}

-- Filtert mért nem lehet Streamre írni?
-- Productivity Checker black magic
-- Actual black magic
-- Streamnek KI KELL TUDNUNK ÉRTÉKELNI A FEJÉT
-- ez fact
-- filter (λ _ → false) s
-- ennek mi a fejeleme?
-- "talán a második" az nem okie dokie
-- filtert nem lehet írni streamre

-- Adjuk vissza egy stream n-edik elemét
get : {A : Set} → ℕ → Stream A → A
get zero sA = head sA
get (suc n) sA = get n (tail sA)

-- mapStream
mapStream : {A B : Set} → (A → B) → Stream A → Stream B
head (mapStream f sA) = f (head sA)
tail (mapStream f sA) = mapStream f (tail sA)
{-
[1,2,3,4,5,....] = sA
|
V
[10,11,12,13,...]
|
snip snip
|
V
[11,12,13,14,...]
-}

-- [a, f a, f (f a), f (f (f a)), ...]
iterate : {A : Set} → (A → A) → A → Stream A
head (iterate f a) = a
tail (iterate f a) = iterate f (f a)

-- ű_l
-- ű_s
_ₗ++ₛ_ : {A : Set} → List A → Stream A → Stream A
[] ₗ++ₛ s = s
head ((x ∷ l) ₗ++ₛ s) = x -- [1 = x, 2,3,4 = l] ++ [asndasbaskds] = [1,2,3,4, dsakjdhasjkdbas] snip snip 1
tail ((x ∷ l) ₗ++ₛ s) = l ₗ++ₛ s

every2nd : {A : Set} → Stream A → Stream A
head (every2nd sA) = head (tail sA)
tail (every2nd sA) = every2nd (tail (tail sA))

{-
every2nd [1,2,3,4,...]
=
[2,4,6,8,...]
-}
