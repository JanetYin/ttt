open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Lib.Equality
open import Lib.Bool
open import Lib.Sum hiding (comm⊎)
open import Lib.Sigma
open import Lib.Unit
open import Lib.Empty

-----------------------------------------

-- Adj meg egy függvényt az alábbi típussal. Hány lényegileg különböző megoldás van?
-- (A lényegileg különböző itt azt jelenti, hogy van olyan bemenet, amire különböző kimenetet ad.)
f : Bool -> Bool -> Bool
f = {!!}

-- Ezzel a típussal is. Hány lényegileg különböző megoldás van?
g : {A : Set} -> A -> A -> A
g = {!!}

-- És erre is ugyanez a kérdés.
h : {A B C : Set} -> A -> B -> C -> B
h = {!!}

-- Miért nincs függvény az alábbi típussal?
i : {A B : Set} -> A -> B
i = {!!}

-----------------------------------------

-- Adottak az alábbi függvények:

flip : {A B : Set} -> A -> (A -> B) -> B
flip n f = f n

add : ℕ -> ℕ -> ℕ
add x y = x + y

-- Mi az alábbi kifejezés típusa, illetve "értéke"? Írd le a levezetést is!
w : {!!}
w n = flip (add 5 (flip 1 (add 2))) (flip n add)

-----------------------------------------

-- Hány különböző eleme van az alábbi típusoknak?
-- Add is meg az összeset! (Csak egy lyukat rakok ide, de csinálj még.

a1 : ⊤ ⊎ Bool
a1 = {!!}

a2 : ⊤ × Bool
a2 = {!!}

a3 : ⊤ ⊎ ⊤
a3 = {!!}

a4 : ⊤ × ⊤
a4 = {!!}

a5 : Bool ⊎ Bool
a5 = {!!}

a6 : Bool × Bool
a6 = {!!}

-- Vélsz szabályszerűséget felfedezni az elemszámokkal kapcsolatban? Milyet?
