module hf04 where

open import Lib
open import Lib.Containers.List
  hiding (head; tail; take; drop; replicate; intersperse; map; splitAt)
open import Lib.Containers.Stream
  hiding (take; drop; repeat; map; splitAt)

-- Adott az alábbi típus:

data Tree (A : Set) : Set where
  leaf : A → Tree A
  node : Tree A → A → Tree A → Tree A

{-
Gyakorlati részen ugyan nem lesz fa; elméleti kérdéshez azonban csak ugyanolyan típusnak számít, mint az összes többi, így természetesen
ilyen típusra kellhet mind β-, mind η-szabályokat megadni.

Adott a fenti Tree típus, mi lesz az eliminátora?
Válasz:

Mik lesznek a β-szabályai?
Válasz:

Mik lesznek az η-szabályai?
Válasz:
-}

-- Definiáld a sumTree függvényt, amely egy fa összes elemét összeadja.
sumTree : Tree ℕ → ℕ
sumTree = {!   !}

{-
Definiáld az isAVLBalanced függvényt, amely egy fáról megállapítja, hogy
AVL fa szerint a fa kiegyensúlyozott-e, tehát csak az az érdekes, hogy
a gyermekek között ne legyen egy mélységnél (magasságnál) nagyobb eltérés.
-}
-- Megj.: A feladat megoldása nem nehéz, cserébe hosszú, sok alapesetet kell figyelembe venni.
isAVLBalanced : {A : Set} → Tree A → Bool
isAVLBalanced = {!   !}

-------------------------------------------------------------
-- β-, η-szabályok még
-------------------------------------------------------------
-- Az alábbi típusok mindegyikének szükséges megadni az eliminátorát,
-- β-szabályait és η-szabályait! Akár Agda kódként is meg lehet írni,
-- a β-szabályok az eliminátor definiálásából kiderülnek.
-- Az η-szabályokat Agda kódként is meg lehetne adni, de ahhoz bizonyítani is kéne,
-- az nem olyan egyszerű most.

data Quintuple (A : Set) : Set where
  QuintupleC : A → A → A → A → A → Quintuple A

-- Eliminátor:
-- β-szabályok:
-- η-szabályok:

data Optional (A : Set) : Set where
  Some : A → Optional A
  None : Optional A

-- Eliminátor:
-- β-szabályok:
-- η-szabályok:

data NonEmpty (A : Set) : Set where
  Last : A → NonEmpty A
  NECons : A → NonEmpty A → NonEmpty A

-- Eliminátor:
-- β-szabályok:
-- η-szabályok:

data NonEmpty2 (A : Set) : Set where
  NECons2 : A → (List A) → NonEmpty2 A

-- Eliminátor:
-- β-szabályok:
-- η-szabályok:

data TriEither (A B C : Set) : Set where
  LeftT : A → TriEither A B C
  MiddleT : B → TriEither A B C
  RightT : C → TriEither A B C

-- Eliminátor:
-- β-szabályok:
-- η-szabályok:

data BiList (A B : Set) : Set where
  ABNil : BiList A B
  ACons : A → BiList A B → BiList A B
  BCons : B → BiList A B → BiList A B

-- Eliminátor:
-- β-szabályok:
-- η-szabályok:

data RoseTree (A : Set) : Set where
  RoseLeaf : A → RoseTree A
  RoseNode : List (RoseTree A) → RoseTree A

-- Eliminátor:
-- β-szabályok:
-- η-szabályok:

data SkipList (A : Set) : Set where
  Skip : SkipList A → SkipList A
  SCons : A → SkipList A → SkipList A
  SNil : SkipList A

-- Eliminátor:
-- β-szabályok:
-- η-szabályok:

data CrazyType (A : Set) : Set where
  C1 : A → A → CrazyType A
  C2 : A → ℕ → CrazyType A
  C3 : CrazyType A → CrazyType A

-- Eliminátor:
-- β-szabályok:
-- η-szabályok:

data SplitTree (A B : Set) : Set where
  SplitTreeNode : Tree A → A → B → Tree B → SplitTree A B

-- Eliminátor:
-- β-szabályok:
-- η-szabályok:

data Join (A B : Set) : Set where
  JoinC : (A → A → B) → Join A B

-- Eliminátor:
-- β-szabályok:
-- η-szabályok:

data CrazyType2 (A B : Set) : Set where
  SingleA : A → CrazyType2 A B
  SingleB : B → CrazyType2 A B
  Translate : (A → B) → CrazyType2 A B

-- Eliminátor:
-- β-szabályok:
-- η-szabályok:

-------------------------------------------------------------
-- β-, η-szabályok koinduktív típusokon
-------------------------------------------------------------
-- Az alábbiakban koinduktív típusok vannak megadva, értelemszerűen ezeknek a konstruktorát kell megadni,
-- illetve a β- és η-szabályukat.

record CoList (A : Set) : Set where
  coinductive
  field
    headTail : Maybe (A × CoList A)

-- Konstruktor:
-- β-szabályok:
-- η-szabályok:

record Infinitree (A : Set) : Set where
  coinductive
  field
    point : A
    left : Infinitree A
    right : Infinitree A

-- Konstruktor:
-- β-szabályok:
-- η-szabályok:

record CoCrazyType (A B : Set) : Set where
  coinductive
  field
    elementA : A
    elementB : B
    build : Maybe (CoCrazyType A B)

-- Konstruktor:
-- β-szabályok:
-- η-szabályok:

-------------------------------------------------------------
{-
Definiáld a halfList függvényt, amely egy véges lista minden második elemét eldobja.
(Tehát az elsőt megtartja, másodikat eldobja, harmadikat megint megtartja, stb.)
Add meg helyesen a függvény típusát is!
-}
halfList : {!!}
halfList = {!!}

halfList-test1 : halfList {ℕ} (1 ∷ 2 ∷ 3 ∷ []) ≡ (1 ∷ 3 ∷ [])
halfList-test1 = refl

halfList-test2 : halfList {ℕ} (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ (1 ∷ 3 ∷ [])
halfList-test2 = refl

halfList-test3 : halfList {ℕ} (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ []) ≡ (1 ∷ 3 ∷ 5 ∷ 7 ∷ [])
halfList-test3 = refl

halfList-test4 : {A : Set} → (λ (x : A) y z → halfList (x ∷ y ∷ z ∷ [])) ≡ (λ (x : A) y z → x ∷ z ∷ [])
halfList-test4 = refl

--------------------------------------------------------------

from : ℕ → Stream ℕ
head (from n) = n
tail (from n) = from (suc n)

{-
Definiáld az interleave függvényt, amely két végtelen listát úgy fűz össze,
hogy először az első lista első elemét veszi, majd a másik lista első elemét,
majd az első lista második elemét, stb. Tehát felváltva veszi a függvény egyenként
az elemeket a listákból.
(Tesztekhez kell, gyakorlásnak nem árt, hiszen gyakorlat teszi a mestert.)
-}
interleave : {A : Set} → Stream A → Stream A → Stream A
interleave = {!!}

interleave-test1 : head (interleave (from 0) (from 100)) ≡ 0
interleave-test1 = refl

interleave-test2 : head (tail (interleave (from 0) (from 100))) ≡ 100
interleave-test2 = refl

interleave-test3 : tail (interleave (from 0) (from 100)) ≡ interleave (from 100) (from 1)
interleave-test3 = refl

{-
Órán definiáltuk a _++_ függvényt induktívan.
Most definiáld a _++ₛ_ függvényt, amely egy Stream elejére egy véges hosszú
listát fűz.
-}
_++ₛ_ : {A : Set} → List A → Stream A → Stream A
_++ₛ_ = {!!}

++ₛ-test1 : head ((10 ∷ 20 ∷ 30 ∷ []) ++ₛ from 0) ≡ 10
++ₛ-test1 = refl

++ₛ-test2 : head (tail (tail ((10 ∷ 20 ∷ 30 ∷ []) ++ₛ from 0))) ≡ 30
++ₛ-test2 = refl

++ₛ-test3 : head (tail (tail (tail ((10 ∷ 20 ∷ 30 ∷ []) ++ₛ from 0)))) ≡ 0
++ₛ-test3 = refl

++ₛ-test4 : head (tail (tail (tail (tail (tail ((10 ∷ 20 ∷ 30 ∷ []) ++ₛ from 0)))))) ≡ 2
++ₛ-test4 = refl

{-
Definiáld a halfStream függvényt, amely egy végtelen lista minden második
elemét elhagyja! (Az elsőt megtartja, másodikat eldobja, harmadikat megtartja, stb.)
Add meg a típusát is!
-}
halfStream : {!!}
halfStream = {!!}

halfStream-test1 : tail (halfStream (from 0)) ≡ halfStream (from 2)
halfStream-test1 = refl

halfStream-test2 : head (halfStream (from 0)) ≡ 0
halfStream-test2 = refl

-------------------------------------------------------
-- Véges vagy végtelen? Esetleg mindkettő
-------------------------------------------------------
{-
Az alábbi feladatokban szükséges kitalálni, hogy az azokban megfogalmazott
függvények csak véges vagy csak végtelen, esetleg mindkét fajta listán
definiálható-e!

Ha valamely függvény mindkét módon definiálható, akkor a Stream-mel működő függvény neve
legyen kiegészítve egy kicsi ₛ betűvel.

Pl.
Definiáld a half függvényt, amely minden második elemet elhagy egy listából!

Ez természetesen megoldható mindkét fajta listával, hiszen fentebb a két
függvény (halfList, halfStream) pontosan ezt csinálja.

Ebben az esetben a sima listával működő függvény neve "half" legyen,
a Stream-mel működő pedig "halfₛ".

------------------

Tesztek a fájl alján jóval lentebb vannak, de a tesztek elárulják, hogy melyik
függvény definiálható melyik listával, szóval mindenki saját felelősségére bízom,
hogy melyik utat választja.
-}

{-
Definiáld a _!!_ függvényt, amely egy lista n. elemét adja vissza 0-tól indexlve.
Az első paraméter a lista, második a szám.
-}

{-
Definiáld a take függvényt, amely egy lista első n elemét tartja meg.
(Ha létezik annyi. Ha nem, akkor annyit tart meg, amennyit bír.)
-}

{-
Definiáld a drop függvényt, amely egy lista első n elemét eldobja.
(Ha létezik annyi. Ha nem, akkor annyit dob el, amennyit bír.)
-}

{-
Definiáld a replicate függvényt, amely egy n elemű azonos elemből álló listát állít elő.
-}

{-
Definiáld a repeat függvényt,
amely azonos elemekből álló végtelen listát állít elő.
-}

{-
Definiáld a map függvényt, amely egy lista minden elemére alkalmaz egy függvényt.
-}

{-
Definiáld az empties függvényt, amely egy listák listáján megállapítja, hogy
mely listák üresek. Amely indexen szereplő lista üres, ott az eredményben azonos indexen true érték legyen,
ellenkező esetben false legyen.
-}

{-
Definiáld az intersperse függvényt, amely egy elemet beszúr minden
listaelem közé.
-}

{-
Definiáld a splitAt függvényt, amely egy listát egy adott indexnél
két részre bont. (Ha véges a lista és nagyobb az index, akkor a lista
után történne a bontás, így úgy is kell kezelni.)
-}

-- NEHÉZ FELADAT
{-
Definiáld a splitOn függvényt, amely egy listát adott tulajdonságú elemek
mentén felbont több listára.
-}

-- NEHÉZ FELADAT
{-
Definiáld a cycle függvényt, amely egy nem üres lista elemeit ciklikusan
ismételgeti a végtelenségig.
Segítség: Érdemes megint a refinement type-ot használni hozzá.
-}






























-- Errefelé lesznek a tesztek. Ha még nem izgat, hogy melyik 
-- függvény hogyan definiálható, akkor ne menj ennél tovább.

-- Ha csak definiálni szeretnél függvényeket, akkor
-- menj tovább, a tesztekből kiderül minden,
-- ne felejtsd visszakommentelni a teszteket.
























------------------------------------------
{-
!!ₛ-test1 : from 0 !!ₛ 3 ≡ 3
!!ₛ-test1 = refl

!!ₛ-test2 : from 0 !!ₛ 100 ≡ 100
!!ₛ-test2 = refl

!!ₛ-test3 : halfStream (from 0) !!ₛ 10 ≡ 20
!!ₛ-test3 = refl

!!ₛ-test4 : (λ (x : Bool) xs → (x ∷ xs) !!ₛ 0) ≡ (λ x xs → x)
!!ₛ-test4 = refl
-}
------------------------------------------
{-
take-test1 : (λ xs → take {ℕ} 0 xs) ≡ (λ xs → [])
take-test1 = refl

take-test2 : take 3 (true ∷ []) ≡ true ∷ []
take-test2 = refl

take-test3 : take {ℕ} 3 (9 ∷ 8 ∷ 5 ∷ 10 ∷ []) ≡ (9 ∷ 8 ∷ 5 ∷ [])
take-test3 = refl

take-test4 : take {ℕ} 4 (9 ∷ 8 ∷ 5 ∷ 10 ∷ []) ≡ (9 ∷ 8 ∷ 5 ∷ 10 ∷ [])
take-test4 = refl

take-test5 : (λ xs → take {ℕ} 2 (9 ∷ 8 ∷ xs)) ≡ (λ xs → 9 ∷ 8 ∷ [])
take-test5 = refl
-}
{-
takeₛ-test1 : takeₛ 3 (from 0) ≡ 0 ∷ 1 ∷ 2 ∷ []
takeₛ-test1 = refl

takeₛ-test2 : (λ xs → takeₛ {Bool} 0 xs) ≡ (λ xs → [])
takeₛ-test2 = refl

takeₛ-test3 : takeₛ 5 (halfStream (from 5)) ≡ 5 ∷ 7 ∷ 9 ∷ 11 ∷ 13 ∷ []
takeₛ-test3 = refl
-}
------------------------------------------
{-
drop-test1 : drop {ℕ} 3 [] ≡ []
drop-test1 = refl

drop-test2 : (λ xs → drop {ℕ} 0 xs) ≡ (λ xs → xs)
drop-test2 = refl

drop-test3 : drop 2 (true ∷ false ∷ true ∷ []) ≡ true ∷ []
drop-test3 = refl

drop-test4 : drop 3 (true ∷ false ∷ true ∷ []) ≡ []
drop-test4 = refl

drop-test5 : drop 4 (true ∷ false ∷ true ∷ []) ≡ []
drop-test5 = refl
-}
{-
dropₛ-test1 : dropₛ 5 (from 0) ≡ from 5
dropₛ-test1 = refl

dropₛ-test2 : dropₛ 0 (from 0) ≡ from 0
dropₛ-test2 = refl

dropₛ-test3 : (λ xs → dropₛ {Bool} 0 xs) ≡ (λ xs → xs)
dropₛ-test3 = refl

dropₛ-test4 : dropₛ 5 (halfStream (from 0)) ≡ halfStream (from 10)
dropₛ-test4 = refl
-}
------------------------------------------
{-
replicate-test1 : {A : Set} → (λ (x : A) → replicate 5 x) ≡ (λ x → x ∷ x ∷ x ∷ x ∷ x ∷ [])
replicate-test1 = refl

replicate-test2 : replicate 3 true ≡ true ∷ true ∷ true ∷ []
replicate-test2 = refl

replicate-test3 : replicate 0 ≡ (λ (x : Bool) → [])
replicate-test3 = refl

replicate-test4 : ∀ n → length {_} {ℕ} (replicate n 0) ≡ n
replicate-test4 zero = refl
replicate-test4 (suc n) rewrite replicate-test4 n = refl
-}
------------------------------------------
{-
repeatₛ-test1 : head (repeatₛ {ℕ} 0) ≡ 0
repeatₛ-test1 = refl

repeatₛ-test2 : head (tail (repeatₛ {ℕ} 1)) ≡ 1
repeatₛ-test2 = refl

repeatₛ-test3 : tail (repeatₛ {ℕ} 1) ≡ repeatₛ 1
repeatₛ-test3 = refl

repeatₛ-test4 : {A : Set} → (λ (x : A) → tail (repeatₛ x)) ≡ repeatₛ
repeatₛ-test4 = refl
-}
------------------------------------------
{-
map-test1 : map {ℕ} suc (1 ∷ 3 ∷ 0 ∷ []) ≡ 2 ∷ 4 ∷ 1 ∷ []
map-test1 = refl

map-test2 : {A B : Set} → (λ (f : A → B) → map f []) ≡ (λ f → [])
map-test2 = refl

map-test3 : map {ℕ} (replicate 3) (1 ∷ 9 ∷ []) ≡ (1 ∷ 1 ∷ 1 ∷ []) ∷ (9 ∷ 9 ∷ 9 ∷ []) ∷ []
map-test3 = refl
-}
{-
mapₛ-test1 : head (mapₛ suc (from 0)) ≡ 1
mapₛ-test1 = refl

mapₛ-test2 : takeₛ 5 (mapₛ repeatₛ (from 0)) ≡ (repeatₛ 0) ∷ (repeatₛ 1) ∷ (repeatₛ 2) ∷ (repeatₛ 3) ∷ (repeatₛ 4) ∷ []
mapₛ-test2 = refl
-}
------------------------------------------
{-
empties-test1 : empties {Bool} ([] ∷ [] ∷ []) ≡ true ∷ true ∷ []
empties-test1 = refl

empties-test2 : empties {ℕ} ((1 ∷ []) ∷ (2 ∷ 4 ∷ 9 ∷ []) ∷ (10 ∷ 10 ∷ []) ∷ []) ≡ false ∷ false ∷ false ∷ []
empties-test2 = refl

empties-test3 : empties ((tt ∷ []) ∷ [] ∷ [] ∷ (tt ∷ tt ∷ []) ∷ []) ≡ false ∷ true ∷ true ∷ false ∷ []
empties-test3 = refl
-}
{-
emptiesₛ-test1 : head (emptiesₛ {ℕ} (repeatₛ [])) ≡ true
emptiesₛ-test1 = refl

emptiesₛ-test2 : emptiesₛ {ℕ} (repeatₛ []) !!ₛ 10  ≡ true
emptiesₛ-test2 = refl

emptiesₛ-test3 : takeₛ 4 (emptiesₛ (mapₛ (λ n → replicate {ℕ} n 10) (1 ∷ from 0))) ≡ false ∷ true ∷ false ∷ false ∷ []
emptiesₛ-test3 = refl
-}
------------------------------------------
{-
intersperse-test1 : intersperse {List ℕ} [] ((1 ∷ []) ∷ (2 ∷ 3 ∷ []) ∷ (4 ∷ []) ∷ []) ≡ (1 ∷ []) ∷ [] ∷ (2 ∷ 3 ∷ []) ∷ [] ∷ (4 ∷ []) ∷ []
intersperse-test1 = refl

intersperse-test2 : intersperse {ℕ} 0 (4 ∷ 6 ∷ 11 ∷ 1 ∷ 0 ∷ 2 ∷ []) ≡ 4 ∷ 0 ∷ 6 ∷ 0 ∷ 11 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 2 ∷ []
intersperse-test2 = refl

intersperse-test3 : (λ x → intersperse {ℕ} x (4 ∷ 6 ∷ 2 ∷ [])) ≡ (λ a → 4 ∷ a ∷ 6 ∷ a ∷ 2 ∷ [])
intersperse-test3 = refl

intersperse-test4 : (λ (x : ℕ) → intersperse x []) ≡ (λ a → [])
intersperse-test4 = refl

intersperse-test5 : intersperse {ℕ} 10 (9 ∷ []) ≡ 9 ∷ []
intersperse-test5 = refl
-}
{-
intersperseₛ-test1 : head (tail (tail (intersperseₛ {ℕ} 0 (repeatₛ 1)))) ≡ 1
intersperseₛ-test1 = refl

intersperseₛ-test2 : head (tail (intersperseₛ {ℕ} 0 (repeatₛ 1))) ≡ 0
intersperseₛ-test2 = refl

intersperseₛ-test3 : takeₛ 10 (intersperseₛ 1 (from 2)) ≡ 2 ∷ 1 ∷ 3 ∷ 1 ∷ 4 ∷ 1 ∷ 5 ∷ 1 ∷ 6 ∷ 1 ∷ []
intersperseₛ-test3 = refl
-}
------------------------------------------
{-
splitAt-test1 : {A : Set} → (λ xs → splitAt {A} 0 xs) ≡ (λ xs → [] , xs)
splitAt-test1 = refl

splitAt-test2 : splitAt {ℕ} 3 (1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ [] , [])
splitAt-test2 = refl

splitAt-test3 : splitAt {ℕ} 3 (1 ∷ 2 ∷ 3 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [] , [])
splitAt-test3 = refl

splitAt-test4 : splitAt {ℕ} 3 (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [] , (4 ∷ []))
splitAt-test4 = refl
-}
{-
splitAtₛ-test1 : splitAtₛ 0 (from 1) ≡ ([] , from 1)
splitAtₛ-test1 = refl

splitAtₛ-test2 : splitAtₛ 4 (from 1) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ [] , from 5)
splitAtₛ-test2 = refl

splitAtₛ-test3 : splitAtₛ 5 (halfStream (from 0)) ≡ (0 ∷ 2 ∷ 4 ∷ 6 ∷ 8 ∷ [] , halfStream (from 10))
splitAtₛ-test3 = refl
-}
------------------------------------------
-- majd a splitOn-hoz egy teszt függvény lesz ez
even : ℕ → Bool
even 0 = true
even 1 = false
even (suc (suc n)) = even n

{-
splitOn-test1 : (λ p → splitOn {ℕ} p []) ≡ (λ p → [] ∷ [])
splitOn-test1 = refl

splitOn-test2 : splitOn (_==ᵇ 2) (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (1 ∷ []) ∷ (3 ∷ 4 ∷ 5 ∷ []) ∷ []
splitOn-test2 = refl

splitOn-test3 : splitOn (_==ᵇ 2) (1 ∷ 2 ∷ 3 ∷ 4 ∷ 2 ∷ []) ≡ (1 ∷ []) ∷ (3 ∷ 4 ∷ []) ∷ [] ∷ []
splitOn-test3 = refl

splitOn-test4 : splitOn even (1 ∷ 2 ∷ 3 ∷ 4 ∷ 2 ∷ []) ≡ (1 ∷ []) ∷ (3 ∷ []) ∷ [] ∷ [] ∷ []
splitOn-test4 = refl

splitOn-test5 : splitOn even (10 ∷ 1 ∷ 3 ∷ 4 ∷ []) ≡ [] ∷ (1 ∷ 3 ∷ []) ∷ [] ∷ []
splitOn-test5 = refl

splitOn-test6 : splitOn even (1 ∷ 3 ∷ 4 ∷ 6 ∷ 7 ∷ []) ≡ (1 ∷ 3 ∷ []) ∷ [] ∷ (7 ∷ []) ∷ []
splitOn-test6 = refl
-}
------------------------------------------
{-
cycleₛ-test1 : takeₛ 10 (cycleₛ {ℕ} (1 ∷ 2 ∷ 3 ∷ []) tt) ≡ 1 ∷ 2 ∷ 3 ∷ 1 ∷ 2 ∷ 3 ∷ 1 ∷ 2 ∷ 3 ∷ 1 ∷ []
cycleₛ-test1 = refl

cycleₛ-test2 : takeₛ 4 (cycleₛ (true ∷ []) tt) ≡ true ∷ true ∷ true ∷ true ∷ []
cycleₛ-test2 = refl

cycleₛ-test3 : takeₛ 7 (cycleₛ {ℕ} (10 ∷ 20 ∷ []) tt) ≡ 10 ∷ 20 ∷ 10 ∷ 20 ∷ 10 ∷ 20 ∷ 10 ∷ []
cycleₛ-test3 = refl
-}
