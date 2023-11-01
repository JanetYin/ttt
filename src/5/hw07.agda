open import Lib hiding (_+∞_)
open import Lib.Containers.Stream hiding (coiteStream)

-- Összegezd egy Stream ℕ első n elemét.
sumn : {A : Set} → ℕ -> Stream ℕ -> ℕ
sumn = {!!}

-- Általánosítva: egy tetszőleges kétparaméteres operátort kapsz;
-- ezt kell végrehajtani az első n elemen, jobbra zárójelezve.
-- A kezdőértéket is megkapod.
-- Pl. foldrStream (_+_) 10 5 (from 0) = (0 + (1 + (2 + (3 + (4 + 10))))).
foldrStream : ∀{i j}{A : Set i}{B : Set j}
                -> (A -> B -> B) -> B -> ℕ -> Stream A -> B
foldrStream = {!!}

-- Az új Streamben legyen az elsőnek az első eleme,
-- aztán a másodiknak az első eleme,
-- aztán az elsőnek a második eleme,
-- aztán a másodiknak a második eleme stb.
interleave : {A : Set} → Stream A → Stream A → Stream A
interleave = {!!}

-- Hasonlóan, csak három Streammel:
-- az első Stream első eleme,
-- a második Stream első eleme,
-- a harmadik Stream első eleme,
-- az első Stream második eleme stb.
interleave3 : {A : Set} → Stream A → Stream A → Stream A → Stream A
interleave3 = {!!}

-- Miért nem lehet az alábbit definiálni?
-- (A dropWhile eldobja az elemeket
-- egészen addig, amíg egyszer olyat nem talál,
-- amire a predikátum hamis.)
dropWhileS : {A : Set} → (A → Bool) → Stream A → Stream A
dropWhileS P xs = {!!}

-- Írd újra a coiteStreamet:
-- lesz egy A típusú "seedünk";
-- az éppen aktuális elemet az A -> B függvénnyel generáljuk,
-- a következő seedet pedig az A -> A függvénnyel.
coiteStream : ∀{i j}{A : Set i}{B : Set j} → (A → A) → (A → B) → A → Stream B
coiteStream = {!!}

-- Írd újra a mapStreamet:
-- az összes elemre hívj meg egy függvényt,
-- és annak az eredményét tedd az új Streambe.
mapStream : ∀{i j}{A : Set i}{B : Set j} → (A → B) → Stream A → Stream B
mapStream = {!!}

-- Nehéz feladat:
-- gondolkodj el, hogyan lehetne egy olyan Stream-szerű konténert definiálni,
-- ami véges is lehet.


------------------------------------------

-- Picit ℕ∞-hoz is (bár abból csak nagyon könnyűeket fogok tudni adni röpin).

-- Növelj meg egy ℕ∞-ot eggyel
-- (persze ha a végtelenről van szó, ennek nem lesz hatása).
suc∞ : ℕ∞ -> ℕ∞
suc∞ = {!!}

-- Konvertálj egy ℕ-ot a megfelelő ℕ∞-ba.
ℕtoℕ∞ : ℕ -> ℕ∞
ℕtoℕ∞ = {!!}

-- Fordítva, ℕ∞-ból ℕ-ba miért nem lehet?

-- Próbáld meg magad is megírni az összeadást.
_+∞_ : ℕ∞ -> ℕ∞ -> ℕ∞
_+∞_ = {!!}
