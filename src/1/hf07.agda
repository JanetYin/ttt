module hf07 where

open import Lib

{-
-- Ezek a függvények a Lib-ben elérhetők ezen a néven így, ezek használhatók nyugodtan!

contradiction : ∀{i j}{P : Set i}{Whatever : Set j} → P → ¬ P → Whatever
contradiction p ¬p = exfalso (¬p p)

contraposition : ∀{i j}{P : Set i}{Q : Set j} → (P → Q) → ¬ Q → ¬ P
contraposition f ¬q p = contradiction (f p) ¬q

weaken : {X : Set} → X → ¬ ¬ X
weaken x = λ ¬x → ¬x x
-}

----------------------------------------------
-- Elmélet -- formalizálás
----------------------------------------------

module F1 where

  -- Ha bementem dolgozni, akkor kapok fizetést.
  form1 : Set
  form1 = {!!}

  -- Ha kapok fizetést és nem maradtam otthon, akkor bementem dolgozni.
  form2 : Set
  form2 = {!!}

  -- Bementem dolgozni és nem maradtam otthon.
  form3 : Set
  form3 = {!!}

  -- Kapok fizetést.
  K : Set
  K = {!!}

  -- Írd fel, majd bizonyítsd vagy cáfold, hogy az első három állításból következik a K.
  proofK : Dec {lzero} {!!}
  proofK = {!!}

----------------------------------------------
-- Gyakorlat maradékja + e9, e10, f4' újak
----------------------------------------------

-- Órán volt, nem baj, ismétlés a tudás atyja.

dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 = {!   !}

dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b = {!   !}

nocontra : {X : Set} → ¬ (X ↔ ¬ X)
nocontra = {!   !}

¬¬invol₁ : {X : Set} → ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
¬¬invol₁ = {!   !}

¬¬invol₂ : {X : Set} → ¬ ¬ ¬ X ↔ ¬ X
¬¬invol₂ = {!   !}

nndnp : {X : Set} → ¬ ¬ (¬ ¬ X → X)
nndnp = {!   !}

dec2stab : {X : Set} → (X ⊎ ¬ X) → (¬ ¬ X → X)
dec2stab = {!   !}

-- Ez az import szolgáltatja a yes/no pattern-öket. Dec-cel érdemes használni.
-- Ha eldöntöttük, hogy teljesül, akkor a sort yes-szel kell kezdeni. (Ez az inl szinonímája.)
-- Ha eldöntöttük, hogy nem teljesül, akkor a sort no-val kell kezdeni. (Ez az inr szinonímája.)

-- open import Lib.Dec.PatternSynonym

e3 : {X : Set} → Dec (¬ (X → (¬ X → X)))
e3 = {!   !}

e4 : Dec ℕ
e4 = {!   !}

e5 : Dec ⊥
e5 = {!   !}

e6 : {X : Set} → Dec (⊥ → X ⊎ ¬ X)
e6 = {!   !}

e7 : {X : Set} → Dec (X × ¬ X → ¬ X ⊎ X)
e7 = {!   !}

e8 : {X : Set} → Dec ((X → X) → ⊥)
e8 = {!   !}

e9 : {X Y : Set} → Dec (X ⊎ Y ↔ (¬ X → Y))
e9 = {!   !}

e10 : {X Y : Set} → Dec ((¬ X → ¬ Y) → Y → X)
e10 = {!   !}

f1 : {X Y : Set} → ¬ ¬ X ⊎ ¬ ¬ Y → ¬ ¬ (X ⊎ Y)
f1 = {!   !}

f2 : ({X Y : Set} → ¬ (X × Y) → ¬ X ⊎ ¬ Y) → {X Y : Set} → ¬ ¬ (X ⊎ Y) → ¬ ¬ X ⊎ ¬ ¬ Y
f2 = {!   !}

----------------------------------------------------------
-- PÉLDÁK ILYEN KINÉZETŰ Dec-ekre!

{-
Adott az alábbi logikai állítás, el kell dönteni, hogy teljesül-e vagy sem.

f3 : Dec ((X Y : Set) → X ⊎ Y → Y)
f3 = ?

Hogy lehet ezt ellenőrizni?
Alapvetően az állítás most még nulladrendű, a (: Set) utáni rész az állítás.
Nulladrend esetén a legegyszerűbb az állítást az ismert igazságtáblával ellenőrizni, hogy teljesül-e (logikából tudjuk, hogy a szintaktika és szemantika helyes és teljes).
Megj.: Az egyetlen csapda a már látott X ⊎ ¬ X vagy ¬ ¬ X → X féle állítások, amik konstruktívan nem bizonyíthatók, pedig a táblából az fog kijönni, hogy igazak. Ekkor ezek duplanegálással bizonyíthatók.

A fenti állításhoz az alábbi táblát tudjuk készíteni:
Az első oszlopok a (: Set) előtt megjelenő betűk, ítéletváltozók, aztán az összes részállítások (a nyilakkal elválasztott állítások).
Majd a legvégére kerüljön a teljes állítás, abból egyszerűbb eldönteni, hogy állításunk teljesül-e, illetve ha nem teljesül, akkor egyszerű eldönteni belőle, hogy mikor nem teljesül.

| X | Y | X ⊎ Y | X ⊎ Y → Y
|---|---|-------|----------
| i | i |   i   | i ⊃ i = i
|---|---|-------|----------
| i | h |   i   | i ⊃ h = h
|---|---|-------|----------
| h | i |   i   | h ⊃ i = i
|---|---|-------|----------
| h | h |   h   | h ⊃ h = i

Az implikáció műveletet meg kell szokni, hogy hogyan működik; csak akkor hamis, ha az állítás eleje igaz, de a vége hamis.
A táblázat utolsó oszlopából láthatjuk, hogy lesz olyan pont, ahol nem teljesül az állítás.
Ennek a vizsgálatára MINDIG a teljes állítást kell nézni, tehát a javasolt módszer alapján az utolsó oszlopot.

Az órán megbeszéltük, hogy a hamisságot a 0 elemű típusok kódolják el, az igazságot pedig a legalább 1 elemű típusok.
Ugyan bármelyik típus használható, Fin 0 is jó hamisnak, 0 ≡ 1 is jó hamisnak, Fin 1 is jó igaznak, Bool is jó igaznak, ℕ is jó igaznak.
Azonban azt javaslom, hogy az igaz elkódolására használjuk a ⊤-ot, míg hamis elkódolására a ⊥-ot.

Alakítsuk át a táblát ez alapján. Ugyanaz a tábla, csak i és h helyett jelöljük azokat ⊤-pal és ⊥-mal.
(Megj.: A továbbiakban a nulladrendű állításokat így írom fel csak.)

| X | Y | X ⊎ Y | X ⊎ Y → Y
|---|---|-------|----------
| ⊤ | ⊤ |   ⊤   |     ⊤
|---|---|-------|----------
| ⊤ | ⊥ |   ⊤   |     ⊥
|---|---|-------|----------
| ⊥ | ⊤ |   ⊤   |     ⊤
|---|---|-------|----------
| ⊥ | ⊥ |   ⊥   |     ⊤

Ekkor X és Y jelöli a konkrét típusokat, míg a többi oszlop azt jelöli, hogy az ott felírt állítás bizonyítható-e.

Láthatjuk, hogy van egy sor, ahol a teljes állítás nem teljesül (ez a 2. sor).
Tehát eldöntöttük, hogy állítás nem teljesül mindig (nem tautológia), ekkor meg is kell adni azt az interpretációt.


f3 : Dec ((X Y : Set) → X ⊎ Y → Y)
f3 = inr ?

A ? helyén egy ((X Y : Set) → X ⊎ Y → Y) → ⊥ típusú értéket kell megadni.
                                         ^ Ezen nyíl miatt tudjuk, hogy ez csak egy függvény, ezt felvehetjük, mint hipotézist (logika ezt hívja dedukciós tételnek).

f3 : Dec ((X Y : Set) → X ⊎ Y → Y)
f3 = inr (λ f → ?)

f : (X Y : Set) → X ⊎ Y → Y

Most ? helyén egy ⊥ típusú értéket kell előállítani, lényegében azt kéri a feladat, hogy mutassuk meg, hogy mikor nem teljesül az állítás.
Ilyenkor nincs más dolgunk, mint megnézni a táblázatot, választani egy sort, ahol az állítás nem teljesül (más példában lehet több hely is, ahol nem teljesül, de az teljesen mindegy, hogy melyiket választjuk),
majd annak a sornak a megfelelő értékeit kell közvetlen átadni az f függvénynek.

Megnézzük a 2. sort, látjuk, hogy X = ⊤, Y = ⊥ esetén az állítás nem működik. Ezeket a típusokat csak át kell adni ebben a sorrendben az f függvénynek.

f3 : Dec ((X Y : Set) → X ⊎ Y → Y)
f3 = inr (λ f → f ⊤ ⊥ ?)

Ekkor ? helyén már csak azt kell bizonyítani, hogy ⊤ ⊎ ⊥ bizonyítható-e. Természetesen igen, inl tt megoldja.
-}

f3 : Dec ((X Y : Set) → X ⊎ Y → Y)
f3 = inr (λ f → f ⊤ ⊥ (inl tt))

-- És kész is van a bizonyítás.
{-
Persze ezt sokkal gyorsabb sima GONDOLKODÁS útján kitalálni. Cáfolás esetén mindig megkapjuk a teljes állítást és ⊥-ot kell belőle előállítani.
Ránézésre tudjuk, hogy egyedül a felvett állítás adhat vissza ⊥-ot az esetek 100%-ában (ez mindig igaz), és ezen specifikus esetben csak akkor lehet ⊥ az eredmény, ha Y = ⊥.
Így Y = ⊤ eseteket nem is kell nézni, teljesen felesleges. 4 eset helyett elég csak 2-t megvizsgálni, X = ⊤-ot és X = ⊥-ot, hogy történik-e valami különleges.
-}

{-

Nézzünk egy másik példát:

f5 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f5 = ?

Ugyanazon módszer, mint az előbb, táblázat:
(A függvényben X Y Z sorrendben vannak, szóval vegyük fel ezeket ugyanígy.)

| X | Y | Z | (X → Z) × (Y → Z) | X × Y → Z | (X → Z) × (Y → Z) → (X × Y → Z)
|---|---|---|-------------------|-----------|--------------------------------
| ⊤ | ⊤ | ⊤ |         ⊤         |    ⊤      |               ⊤
|---|---|---|-------------------|-----------|--------------------------------
| ⊤ | ⊤ | ⊥ |         ⊥         |    ⊥      |               ⊤
|---|---|---|-------------------|-----------|--------------------------------
| ⊤ | ⊥ | ⊤ |         ⊤         |    ⊤      |               ⊤
|---|---|---|-------------------|-----------|--------------------------------
| ⊤ | ⊥ | ⊥ |         ⊥         |    ⊤      |               ⊤
|---|---|---|-------------------|-----------|--------------------------------
| ⊥ | ⊤ | ⊤ |         ⊤         |    ⊤      |               ⊤
|---|---|---|-------------------|-----------|--------------------------------
| ⊥ | ⊤ | ⊥ |         ⊥         |    ⊤      |               ⊤
|---|---|---|-------------------|-----------|--------------------------------
| ⊥ | ⊥ | ⊤ |         ⊤         |    ⊤      |               ⊤
|---|---|---|-------------------|-----------|--------------------------------
| ⊥ | ⊥ | ⊥ |         ⊤         |    ⊤      |               ⊤

Látjuk, hogy az utolsó oszlop csak igazakból áll, tehát az állítás teljesül.

f5 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f5 = inl ?

Ekkor bizonyítanunk kell, hogy az állítás minden X, Y, Z-re működik, tehát meg kell adni a típusnak egy értékét, definiálni kell a függvényt.
Tehát ? helyére egy (X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z) típusú dolog kell.

Hány paraméteres a függvény, amit meg kell adni? Ha megszámoljuk, akkor kijön, hogy eggyel kevesebb (ez mindig helyes), mint ahány oszlopunk van a táblában az utolsó nélkül.
Ezen esetben 4 paraméterünk van (illetve lesz még egy mindjárt), az X, Y, Z, és az (X → Z) × (Y → Z). Bizonyításkor ezek közül maguk az ítéletváltozók, tehát a típusváltozók
teljesen feleslegesek és nem használhatók semmire.

f5 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f5 = inl (λ _ _ _ xzyz → ?)

Ekkor ? helyére X × Y → Z típusú érték kell. Látjuk, hogy függvényt kell eredményül visszaadni (avagy a logika dedukciós tétele miatt), ezért lambdát írunk és felvesszük a maradék
1 paramétert is.

f5 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f5 = inl (λ _ _ _ xzyz → λ xy → ?)

Ezt lerövidítem, mert ugyanazt jelenti:

f5 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f5 = inl (λ _ _ _ xzyz xy → ?)

? helyére most már csak Z-t kell adni.
xzyz és xy mind rendezett párok, ezekre érdemes mintailleszteni. (Mindenre érdemes mintailleszteni, aminek túl konkrét a típusa, tehát van benne × vagy ⊎.)

Lambdában kétfélét mutattam, hogy hogyan lehet illeszteni, most kiválasztom az egyiket, persze a másikkal is lehet. Vagy akár lehet rá segédfüggvényt is írni.

f5 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f5 = inl (λ where _ _ _ (xz , yz) (x , y) → ?)

Ezen a ponton kétféleképpen is elő tudunk állítani egy Z-t, a feladat szempontjából teljesen mindegy, hogy melyiket választjuk.

Az egyiket ideírom kommentbe, a másikat rendesen kódként.

f5 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f5 = inl (λ where _ _ _ (xz , yz) (x , y) → xz x)
-}

f5 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f5 = inl (λ where _ _ _ (xz , yz) (x , y) → yz y)

---------------------------------------------------------

f4 : Dec ((X Y Z : Set) → (X → Z) ⊎ (Y → Z) → (X ⊎ Y → Z))
f4 = {!!}

f4' : Dec ((X Y Z : Set) → (X ⊎ Y → Z) → (X → Z) ⊎ (Y → Z))
f4' = {!!}

f6 : Dec ((X Y Z : Set) → (X × Y → Z) → (X → Z) × (Y → Z))
f6 = {!!}

f7 : Dec ((X Y Z : Set) → (X ⊎ Y × Z) → (X ⊎ Y) × (X ⊎ Z))
f7 = {!!}

f8 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → ((X ⊎ Y) × Z))
f8 = {!!}

f9 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → (X ⊎ Y × Z))
f9 = {!!}
