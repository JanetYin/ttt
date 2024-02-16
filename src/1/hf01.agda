module hf01 where

open import Lib

{-
Definiáld a mul3 függvényt, amely 3-mal megszoroz egy természetes számot!
Add meg a függvény helyes típusát is!
Tipp: értelemszerűen ha van + függvény, akkor van a neki megfelelő szorzás is,
de rábízom mindenkire, hogy kitalálja, hogy mi a neve agdában.
-}
mul3 : {!   !}
mul3 = {!   !}

{-
Add meg ugyanúgy a mul3 függvényt, de most egy különböző módon,
tehát ha az elsőben lambda volt, akkor ebben ne úgy legyen
vagy fordítva. És ne mul3' = mul3 legyen a definíció!
-}
mul3' : {!   !}
mul3' = {!   !}

{-
Agdában nagyon egyszerű unit teszteket írni, mindenféle framework
és hasonlók nélkül, ez magában a nyelvben benne van.
-}
mul3-test1 : mul3 10 ≡ 30
mul3-test1 = refl

mul3-test2 : mul3 0 ≡ 0
mul3-test2 = refl

mul3-test3 : mul3 2 ≡ 6
mul3-test3 = refl

mul3-test4 : mul3 5 ≡ 15
mul3-test4 = refl

mul3-test5 : mul3 100 ≡ 300
mul3-test5 = refl

mul3'-test1 : mul3' 10 ≡ 30
mul3'-test1 = refl

mul3'-test2 : mul3' 0 ≡ 0
mul3'-test2 = refl

mul3'-test3 : mul3' 2 ≡ 6
mul3'-test3 = refl

mul3'-test4 : mul3' 5 ≡ 15
mul3'-test4 = refl

mul3'-test5 : mul3' 100 ≡ 300
mul3'-test5 = refl

mul3= : ∀{n} → mul3 n ≡ mul3' n
mul3= = refl

{-
Azt már megbeszéltük, hogy hány darab A → A típusú függvény létezik,
ugye pontosan 1, bármi más legalább propozicionálisan (tehát működésben) egyenlő lesz ezzel az egy függvénnyel.
-}
id' : {A : Set} → A → A
id' x = x

-- Hány darab (A → A) → A típusú függvény létezik?
-- Definiáld az összeset vagy legalább 8-at!



{-
Definiáld a thrice függvényt, amely egy függvényt
egy adott értékre háromszor alkalmaz!
Add meg a függvény típusát is!
-}
thrice : ∀{i}{A : Set i} → {!   !}
thrice = {!   !}

{-
Nehéz feladat!
Alkalmazzuk n-szer a függvényt egy értékre.
Tipp: Csak azért nehéz, mert nem meséltem még a mintaillesztésről,
de triviális módon agdában is lehet mintailleszteni, mint ahogy haskellben,
azonban a természetes számok nem csak úgy "vannak" ebben a világban.
Lyukba ha beírod a mintailleszteni kívánt változó nevét, majd C-c C-c
billentyűkombinációt nyomva agda automatikusan mintailleszt.
Illetve ez az első pont, ahol rekurzió is szükséges a megoldáshoz.
-}
recℕ : ∀{i}{A : Set i} → (A → A) → A → ℕ → A
recℕ = {!   !}


{-
Agdát lehet és érdemes is használni az előadás kvízfeladatok megoldásához.
Ha a kérdésben szereplő megfelelő kifejezést Agdában megfogalmazzuk, akkor
Agda gyorsan tud választ adni. Ehhez persze gyakorolni kell az Agda használatát,
mert esetenként nem egyszerű megfogalmazni azt, amit a feladat kér.
Ha ezt a lyukat sikerül kitölteni a C-c C-r-rel, akkor megtudjuk, hogy
a két identitás függvény valójában teljesen egyenlők.
-}
id= : ∀{i}{A : Set i} → (λ (x : A) → x) ≡ (λ y → y)
id= = {!   !}

{-
Definiálj két függvényt, f1, f2, amelyekre teljesülnek az alábbiak:
-- f1 ℕ _*_ 0 = f2 ℕ _*_ 0
-- f1 ℕ _+_ 2 ≠ f2 ℕ _+_ 2
-}
f1 f2 : (A : Set) → (A → A → A) → A → A
f1 = ?
f2 = ?

f1-f2₁ : f1 ℕ _*_ 0 ≡ f2 ℕ _*_ 0
f1-f2₁ = refl

f1-f2₂ : f1 ℕ _+_ 2 ≢ f2 ℕ _+_ 2
f1-f2₂ ()