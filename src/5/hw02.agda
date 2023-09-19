open import Lib

-- Hány eleme van az alábbi típusoknak? Add meg az összeset (ha lehet).
a1 {-a2 a3 ...-} : Bool × Bool
a1 = {!!}
-- a2 = ?
-- a3 = ?
-- Itt persze annyit adj meg, ahány elem van.

-- Hasonlóan a későbbieknél is: számold ki, hány elem van, és add meg az összeset.
b1 : Bool ⊎ Bool
b1 = {!!}

c1 : ⊤ × ⊤
c1 = {!!}

d1 : ⊤ × (⊤ ⊎ ⊤)
d1 = {!!}

e1 : (⊤ × ⊤) ⊎ ⊤
e1 = {!!}

f1 : ⊥ ⊎ (⊤ ⊎ ⊥)
f1 = {!!}

g1 : (⊥ ⊎ ⊤) × ⊥
g1 = {!!}

h1 : (ℕ × ⊥) ⊎ ⊤
h1 = {!!}

i1 : Bool × Bool ⊎ Bool
i1 = {!!}

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
