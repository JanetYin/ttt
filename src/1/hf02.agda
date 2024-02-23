module hf02 where

open import Lib hiding (comm⊎)

-- Érdemes a ↔ nyilas feladatokat nézegetni!

-- TÍPUSOK

{-
data ⊥ : Set where

exfalso : ∀{ℓ}{A : Set ℓ} → ⊥ → A
exfalso ()

record _×_ {ℓ κ}(A : Set ℓ)(B : Set κ) : Set (ℓ ⊔ κ) where
  constructor _,_
  field
    fst : A
    snd : B

open _×_ public

_↔_ : ∀{ℓ κ} → Set ℓ → Set κ → Set (ℓ ⊔ κ)
A ↔ B = (A → B) × (B → A)

data _⊎_ {ℓ κ}(A : Set ℓ)(B : Set κ) : Set (ℓ ⊔ κ) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

case : ∀{ℓ κ μ}{A : Set ℓ}{B : Set κ}{C : Set μ} → A ⊎ B → (A → C) → (B → C) → C
case (inl a) a→c b→c = a→c a
case (inr b) a→c b→c = b→c b
-}

-- Típusokról emlékeztető
-- A ⊎ B = Vagy A-t vagy B-t tárolja egy ilyen típusú kifejezés magában, ezért megadásnál elég az egyiket megadni, viszont ha ilyet kapsz mintaillesztésig nem tudni melyik van benne. Konstruktora inl és inr
-- A × B = A-t és B-t is tárol egy ilyen típusú kifejezést, ezért megadásnál mindkettőt meg kell adni, viszont ha ilyet kapsz akkor garantáltan mindkettő benne lesz. Konstruktora vessző, projekciói fst és snd
-- ⊤ = Egy elemű típus, konstruktora tt
-- ⊥ = Üres típus, nincs eleme.


{-

Konstruktor táblázat:

- Konstruktor: Egy típust előállító primitív függvény ami nem végez számítást, minden kifejezés ami A típusú, A valamelyik konstruktorára illeszkedni fog.

+--------------------+--------------------+
|                    | Konstruktor        |
+--------------------+--------------------+
| A × B              | _,_                |
+--------------------+--------------------+
| A ⊎ B              | inl inr            |
+--------------------+--------------------+
| Bool               | true false         |
+--------------------+--------------------+
| ⊥                  |                    |
+--------------------+--------------------+
| ⊤                  | tt                 |
+--------------------+--------------------+
-}


-- Billentyűkombinációk
-- C-c C-l   - Betölti a fájlt, ezt nyomd meg minden névváltoztatás után
-- C-c C-n   - Kiértékel egy kifejezést
-- C-c C-SPC - Egy hole-ba beír egy adott kifejezést és kitölti
-- C-c C-r   - Egy holeba írt kifejezéssel megpróbálja kitölteni a hole-t vagy ha nincs semmi a holeban bevezet valami egyértelműt (ha van olyan)
-- C-c C-,   - Kiírja azt a típust amilyen típusú kifejezést a holeba kell írni
-- C-c C-c   - Mintailleszt. Ha nem adunk semmit a promptba felvesz mindent paraméterül.

-- Refine (C-c C-r) gyakorlás
-- A következő feladatokat a C-c C-r segítségével old meg!

-- Írj kifejezést az alábbi típusokkal. A kifejezések értéke vagy működése irreleváns, a kombinációk gyakorlása a releváns.
-- Ahelyett, hogy manuálisan írnál a hole köré vagy egyszerre írnád be az egész kifejezést, használj Refine-t (C-c C-r) ha "egyértelmű" mit kell behelyettesíteni:
-- Ha a hole típusa "A → B" alakú, C-c C-r betölt a holeba egy lambdát.
-- Ha a hole típusa "A × B" alakú, C-c C-r betölt a holeba egy ,-t mert az az egyetlen konstruktora (tehát egyértelmű).
-- Ha a hole típusa "⊤" alakú, C-c C-r betölt a holeba tt-t, mert az az egyetlen konstruktora (tehát egyértelmű).
-- Ha a hole típusa "A ⊎ B" alakú, C-c C-r nem tölt be semmit, mert mind az "inl" és az "inr" bevezetése lehet hogy jó. Írj a hole-ba inl-t vagy inr-t és próbáld újra C-c C-r el!

-- Ha a refine azt írja "Cannot refine" akkor amit a hole-ba beleraktál és refineolni próbálsz nem típushelyes.
-- Ha a refine azt írja "Don't know which constructor to introduce of ... or ..." akkor nem egyértelmű, hogy mit vezessen be.

-- PÉLDALEVEZETÉS: ex₁₋₆-on keresztül egy levezetés van megadva, hogy milyen
-- billentyűkombinációra mit kell látni, ha minden jól megy.
ex₁ : ((⊥ → ⊤) ⊎ ⊥) × (⊤ → (⊥ ⊎ (⊤ × Bool)))
ex₁ = {!   !}

-- Egy ×-t (szorzattípust) kell a holeba írni. Ennek egy db konstruktora van, ezért a C-c C-r magától meg tudja oldani

ex₂ : ((⊥ → ⊤) ⊎ ⊥) × (⊤ → (⊥ ⊎ (⊤ × Bool)))
ex₂ = {!   !} , {!   !}

-- Bal oldalt egy (⊥ → ⊤) ⊎ ⊥ típusú kifejezést kell írni. Mivel ⊥-ot nem tudunk ezért a bal oldalt kell választanunk. Beírjuk a hole-ba hogy inl és C-c C-r
-- Jobb oldalt ⊤ → (⊥ ⊎ (⊤ × Bool)) típusú kifejezés kell írni. Mivel ez egy függvény, ezt a C-c C-r magától meg tudja oldani és bevezet egy lambdát.

ex₃ : ((⊥ → ⊤) ⊎ ⊥) × (⊤ → (⊥ ⊎ (⊤ × Bool)))
ex₃ = inl {!   !} , λ x → {!   !}

-- Bal oldalt egy ⊥ → ⊤ típusú kifejezést kell írni, ez egy függvény tehát a C-c C-r magától bevezet egy lambdát.
-- Jobb oldalt ⊥ ⊎ (⊤ × ⊤) típúsú kifejezést kell írni. ⊥-ot elég nehéz lenne magától írni, ezért a jobb oldalt kell választanunk, beírjuk a hole-ba hogy inr és C-c C-r

ex₄ : ((⊥ → ⊤) ⊎ ⊥) × (⊤ → (⊥ ⊎ (⊤ × Bool)))
ex₄ = inl (λ x → {!   !}) , λ x → inr {!   !}

-- Bal oldalt csak egy tt szükséges, ezt C-c C-r ki tudja magától találni.
-- Jobb oldalt ⊤ × Bool szükséges. Ugye ennek csak egy konstruktora van, a "," amit a C-c C-r be tud vezetni magától.

ex₅ : ((⊥ → ⊤) ⊎ ⊥) × (⊤ → (⊥ ⊎ (⊤ × Bool)))
ex₅ = inl (λ x → tt) , λ x → inr ({!   !} , {!   !})

-- Az első hole-ba csak egy tt szükséges, ezt C-c C-r meg tudja oldani.
-- A másodikba egy Bool, itt magától nem tudja eldönteni, mert nem egyértelmű, de az értéke irreleváns ezért itt lehet választani.

ex₆ : ((⊥ → ⊤) ⊎ ⊥) × (⊤ → (⊥ ⊎ (⊤ × Bool)))
ex₆ = inl (λ x → tt) , λ x → inr (tt , true)

-- FELADATOK
-- Írjunk kifejezéseket az alábbi típusokkal!

f₁ : (Bool → ⊥) ⊎ (Bool × ⊤)
f₁ = {!   !}

f₂ : (⊤ → Bool → ⊥ ⊎ ⊥) ⊎ (⊥ → ⊤ × Bool)
f₂ = {!   !}

f₃ : ⊤ → Bool × (⊤ → Bool ⊎ ⊥)
f₃ = {!   !}

-- Tipp: felhasználhatjuk a paraméterül kapott ⊥-okat hogy ⊥-ot "állítsunk elő".

f₄ : (⊥ → ⊤ → ⊥) × (⊥ ⊎ ⊤)
f₄ = {!   !}

f₅ : ⊥ → ⊥ ⊎ ⊥
f₅ = {!   !}

f₆ : (Bool → (⊥ × Bool) ⊎ (⊥ → ℕ)) × (⊥ ⊎ (⊤ × (⊤ × ℕ)))
f₆ = {!   !}

-- Feladatok polimorfizmussal (itt fel kell majd a paramétereket használni, magától a C-c C-r nem old meg mindent)
-- Példa használat polimorf feladatnál:

exp₁ : {A B C : Set} → (A ⊎ (B ⊎ (C × Bool))) → (B → C) → (ℕ × C → A) → A
exp₁ = {!   !}

-- C-c C-r el felvesszük a paraméterek lamdbaként.
-- (itt manuálisan szebb neveket adtam nekik utána)

exp₂ : {A B C : Set} → (A ⊎ (B ⊎ (C × Bool))) → (B → C) → (ℕ × C → A) → A
exp₂ = λ a⊎b⊎c×bool b→c 𝕟×c→a → {!   !}

-- Először, mivel van egy hosszú ⊎ láncunk, arra illeszünk mintát.
-- Rakjunk {-et az a⊎b⊎c×bool elé és a hole után, majd C-c C-l és utána C-c C-c-vel tudunk mintailleszteni, de lehet az ismert case függvényt is használni
-- (a paramétereket manuálisan átneveztem)

exp₃ : {A B C : Set} → (A ⊎ (B ⊎ (C × Bool))) → (B → C) → (ℕ × C → A) → A
exp₃ = λ {a⊎b⊎c×bool b→c 𝕟×c→a → {!   !}}

exp₄ : {A B C : Set} → (A ⊎ (B ⊎ (C × Bool))) → (B → C) → (ℕ × C → A) → A
exp₄ = λ { (inl a) b→c 𝕟×c→a → {!   !} ; (inr b⊎c×bool) b→c 𝕟×c→a → {!   !}}

-- A bal oldali holeba az 'a' kifejezés típusa megfelel.
-- Jobb oldalon megint illeszünk mintát. (már nem kell zárójelezni)

exp₅ : {A B C : Set} → (A ⊎ (B ⊎ (C × Bool))) → (B → C) → (ℕ × C → A) → A
exp₅ = λ { (inl a) b→c 𝕟×c→a → a ; (inr (inl b)) b→c 𝕟×c→a → {!   !} ; (inr (inr c×bool)) b→c 𝕟×c→a → {!   !}}

-- A bal oldali esetben van B típusú kifejezésünk, amiből a b→c függvény segítségével tudunk C típusút csinálni. Ezt és egy random számot át tudunk adni a 𝕟×c→a függvénynek hogy A típusú kifejezést kapjunk.
-- Jobb oldalt van C típusú kifejezésünk ezért azt és egy random számot át tudunk adni a 𝕟×c→a függvénynek.
-- Mivel a c×bool tupleből csak az első elem kell ezért az fst függvényt használjuk, de lehetne mintailleszteni is.

exp₆ : {A B C : Set} → (A ⊎ (B ⊎ (C × Bool))) → (B → C) → (ℕ × C → A) → A
exp₆ = λ { (inl a) b→c 𝕟×c→a → a ; (inr (inl b)) b→c 𝕟×c→a → 𝕟×c→a (0 , b→c b) ; (inr (inr c×bool)) b→c 𝕟×c→a → 𝕟×c→a (1 , (fst c×bool))}

-- FELADATOK
-- Írjunk kifejezéseket az alábbi típusokkal

p₁ : {A B : Set} → A → B → A
p₁ = {!   !}

p₂ : {A B : Set} → (A → B) → A → B
p₂ = {!   !}

p₃ : {A B : Set} → (A × B) → A
p₃ = {!   !}

p₄ : {A : Set} → A ⊎ A → A
p₄ = {!   !}

p₅ : {A B : Set} → (A × (A → B)) → B
p₅ = {!   !}

p₆ : {A B C : Set} → (A → B) → (B → C) → A → C
p₆ = {!   !}

p₇ : {A B C : Set} → (A → B → C) → A × B → C
p₇ = {!   !}

p₈ : {A B C : Set} → (A × B → C) → A → B → C
p₈ = {!   !}

p₉ : {A B C : Set} → (A ⊎ B) → (A → C) → (B → C) → C
p₉ = {!   !}

p₁₀ : {A B C : Set} → A ⊎ (B → A) → A ⊎ B → A
p₁₀ = {!   !}

p₁₁ : {A B : Set} → A ⊎ (⊤ × A) → (A → B) × ℕ → A × B
p₁₁ = {!   !}

p₁₂ : {A B : Set} → (A → A → B) → ((A → B) → A) → B
p₁₂ = {!   !}

-- Új billentyűkombinációk
-- (Ha hole-ba fv kell) C-c C-c ENTER = felveszi a paramétereket
-- Írd meg az alábbi bijekciókat

id↔ : {A : Set} → A ↔ A
id↔ = {!   !}

id↔const : {A B : Set} → (A → A) ↔ (A → B → A)
id↔const = {!   !}

comm⊎ : {A B : Set} → (A ⊎ B) ↔ (B ⊎ A)
comm⊎ = {!   !}

comm× : {A B : Set} → (A × B) ↔ (A × B)
comm× = {!   !}

-- hosszabb
comm↔ : {A B : Set} → (A ↔ B) ↔ (B ↔ A)
comm↔ = {!   !}

r₁ : {A B C : Set} → (A × (B ⊎ C)) ↔ ((C ⊎ B) × A)
r₁ = {!   !}

-- nehezebb
plus0 : {A B : Set} → (A ↔ B) ↔ ((A ⊎ ⊥) ↔ (B ⊎ ⊥))
plus0 = {!   !}

-- nehezebb
times1 : {A B : Set} → (A ↔ B) ↔ ((A × ⊤) ↔ (B × ⊤))
times1 = {!   !}

trans↔ : {A B C : Set} → (A ↔ B) → (B ↔ C) → (A ↔ C)
trans↔ = {!   !}

⊥ext : {A : Set} → (A → ⊥) → A ↔ ⊥
⊥ext = {!   !}

classic : ((Bool → ⊥) → ⊥) ↔ Bool
classic = {!   !}

-- TESZTELT BIJEKCIÓK
-- Ezek olyan bijekciók, amiket meg lehet típushelyesen, de rosszul írni.
-- Ezért automata tesztek vannak hozzájuk csatolva

-- Példa:

^↔ : {A : Set} → (A × A) ↔ (Bool → A)
fst ^↔ x false = fst x
fst ^↔ x true = snd x
snd ^↔ f = f false , f true

-- Itt a bizonyítás azt mondja,
-- hogy minden t : A × A kifejezés esetén ha először az első részét az előző függvénynek alkalmazzuk, majd a másodikat, visszakapjuk az eredeti értéket.
-- Tehát f(g(x)) = x (azaz a bijekció egy definíciója)
bij^↔ : {A : Set}{t : A × A} → snd ^↔ (fst ^↔ t) ≡ t
bij^↔ = refl

-- Ha olyan definíciót adnánk meg, ami ezeket nem tejesíti az agda reklamálna
-- Itt egy hibás eset, ha kikommenteled hibát ír

{-
^↔' : {A : Set} → (A × A) ↔ (Bool → A)
fst ^↔' x _ = fst x
snd ^↔' f = f false , f false

bij^↔' : {A : Set}{t : A × A} → snd ^↔' (fst ^↔' t) ≡ t
bij^↔' = refl
-}

a+a=2a : {A : Set} → (A ⊎ A) ↔ (Bool × A)
a+a=2a = {!   !}

bij-a+a=2a : {A : Set}{t : A}{b : Bool} → fst a+a=2a (snd a+a=2a (b , t)) ≡ (b , t)
bij-a+a=2a {b = true} = refl
bij-a+a=2a {b = false} = refl

a*[b+1]=a*b+a : {A B : Set} → (A × (B ⊎ ⊤)) ↔ ((A × B) ⊎ A)
a*[b+1]=a*b+a = {!   !}

bij-a*[b+1]=a*b+a : {A B : Set}{a : A}{b : B ⊎ ⊤} → snd a*[b+1]=a*b+a (fst a*[b+1]=a*b+a (a , b)) ≡ (a , b)
bij-a*[b+1]=a*b+a {b = inl x} = refl
bij-a*[b+1]=a*b+a {b = inr tt} = refl

-------------------------------------------------------------------------
-- Az oda-vissza nyilas bizonyításokra az alábbi formát javaslom használni
-- Nem kötelező, a gyakorlaton megmutattam, hogy lehet másképp is.
-- ld. idl⊎ a gyakorlatról.
-- Az ↔ valójában csak egy rendezett pár, így a _,_ konstruktort felvesszük,
-- majd két külön függvényként megadjuk a két irányt, így rendesen
-- tudunk mintailleszteni (míg órán láttuk, hogy lambdában nem lehet csak úgy mintailleszteni).
-- A két függvény típusának lemásoljuk pontosan ugyanazt, ami a típusban van,
-- csak a ↔ nyilat a két függvényben a két megfelelő irányra cseréljük,
-- mint ahogy a lenti példában is látható.
assoc⊎ : {A B C : Set} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C)
assoc⊎ = to' , from' where
  to' : {A B C : Set} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
  to' (inl (inl x)) = inl x
  to' (inl (inr x)) = inr (inl x)
  to' (inr x) = inr (inr x)

  from' : {A B C : Set} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
  from' (inl x) = inl (inl x)
  from' (inr (inl x)) = inl (inr x)
  from' (inr (inr x)) = inr x

idr⊎ : {A : Set} → A ⊎ ⊥ ↔ A
idr⊎ = {!   !}

-- (×, ⊤) kommutatív egységelemes félcsoport

assoc× : {A B C : Set} → (A × B) × C ↔ A × (B × C)
assoc× = {!   !}

idl× : {A : Set} → ⊤ × A ↔ A
idl× = {!   !}

idr× : {A : Set} → A × ⊤ ↔ A
idr× = {!   !}

-- ⊥ egy null elem

null× : {A : Set} → A × ⊥ ↔ ⊥
null× = {!   !}

-- disztributivitása a × és az ⊎-nak.

dist : {A B C : Set} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
dist = {!   !}

-- hatványozás törvényei

-- Cᴬˣᴮ = (Cᴬ)ᴮ
curry : ∀{A B C : Set} → (A × B → C) ↔ (A → B → C)
curry = {!   !}

-- Cᴬ⁺ᴮ = Cᴬ * Cᴮ
⊎×→ : {A B C D : Set} → ((A ⊎ B) → C) ↔ (A → C) × (B → C)
⊎×→ = {!   !}

law^0 : {A : Set} → (⊥ → A) ↔ ⊤
law^0 = {!   !}

law^1 : {A : Set} → (⊤ → A) ↔ A
law^1 = {!   !}

law1^ : {A : Set} → (A → ⊤) ↔ ⊤
law1^ = {!   !}

-- (A + B)² = A² + 2AB + B²
iso1 : {A B : Set} → (Bool → (A ⊎ B)) ↔ ((Bool → A) ⊎ Bool × A × B ⊎ (Bool → B))
iso1 = {!   !}

iso2 : {A B : Set} → ((A ⊎ B) → ⊥) ↔ ((A → ⊥) × (B → ⊥))
iso2 = {!   !}

iso3 : (⊤ ⊎ ⊤ ⊎ ⊤) ↔ Bool ⊎ ⊤
iso3 = {!   !}
testiso3 : fst iso3 (inl tt) ≢ fst iso3 (inr (inl tt))
testiso3 ()
testiso3' : fst iso3 (inl tt) ≢ fst iso3 (inr (inr tt))
testiso3' ()
testiso3'' : fst iso3 (inr (inl tt)) ≢ fst iso3 (inr (inr tt))
testiso3'' ()

iso4 : (⊤ → ⊤ ⊎ ⊥ ⊎ ⊤) ↔ (⊤ ⊎ ⊤)
iso4 = {!   !}
testiso4 : fst iso4 (λ _ → inl tt) ≢ fst iso4 (λ _ → inr (inr tt))
testiso4 ()
testiso4' : snd iso4 (inl tt) tt ≢ snd iso4 (inr tt) tt
testiso4' ()

------------------------------------------
-- Magyarázat még a definícionális egyenlőségről:
-- Vegyük az alábbi példát:

_∧₁_ : Bool → Bool → Bool
true ∧₁ true = true
_    ∧₁ _    = false -- a sor elejét agda kiemeli, mert átfedés van az esetek között

_∧₂_ : Bool → Bool → Bool
true ∧₂ b = b
false ∧₂ _ = false
{-
Mi a különbség a két definíció között?
Első ránézésre semmi, mindkettő pontosan ugyanúgy működik.
Azonban ha elkezdünk egy kicsit játszani a két éssel, rögtön kiderül,
hogy különbség nagyon is sok van közöttük, a két függvény teljesen másképp
működik, ebből következően teljesen másképp viselkedik.
Nézzünk példákat erre, hogy is látszódik ez meg.
-}

∧₁-ex1 : true ∧₁ true ≡ true
∧₁-ex1 = refl
-- Ebben semmi meglepő nincs, maga ez a sor a definícióban is ott van.

∧₂-ex1 : true ∧₂ true ≡ true
∧₂-ex1 = refl
-- Definíció szerint az lesz az eredmény, amit a második paraméter helyére
-- helyettesítek.

∧₁-ex2 : true ∧₁ false ≡ false
∧₁-ex2 = refl

∧₂-ex2 : true ∧₂ false ≡ false
∧₂-ex2 = refl
-- Amíg a két érték egyértelműen adott,
-- addig semmi különbséget nem fogunk tapasztalni.

-- Nézzünk egy érdekesebb esetet, ahol érdekességekkel tudunk találkozni.
∧₁-ex3 : (λ a → false ∧₁ a) ≡ (λ a → false)
∧₁-ex3 = refl

∧₂-ex3 : (λ a → false ∧₂ a) ≡ (λ a → false)
∧₂-ex3 = refl
-- Ez az eset még mindig jól működik, definíció szerint ha az első paraméter nem true,
-- akkor az csak false lehet, és abban az esetben az eredmény false,
-- tehát agda ekkor még tud normalizálni.

-- Az alábbi példában találkozunk az igazi érdekességgel.
∧₁-ex4 : (λ a → true ∧₁ a) ≡ (λ a → a)
∧₁-ex4 = {! refl !}

∧₂-ex4 : (λ a → true ∧₂ a) ≡ (λ a → a)
∧₂-ex4 = refl
-- Az ∧₁-es egyenlőség már nem fog teljesülni definíció szerint,
-- mert a második paraméterről is egyértelműen tudni kell, hogy micsoda.
-- Ha megpróbáljuk az ∧₁-es egyenlőséget refl-lel bizonyítani, akkor fordítási hibát kapunk:
-- true ∧₁ a ≠ a of type Bool
-- (Az ∧₁-es egyenlőség bizonyíthatóan teljesül, de nem definíció szerint.)

-- Az ∧₂-es egyenlőség ezzel szemben definíció szerint teljesülni fog, pont így van definiálva,
-- csak az első paramétertől függ, hogy a függvény miként viselkedik.

-- Éppen ezért érdemes a függvényeket megpróbálni úgy definiálni, hogy minél
-- kevesebb paraméterre kelljen mintailleszteni, mert akkor több eset fog definíció szerint működni,
-- amelynél agdában nincs jobb működés.
------------------------------------------
-- ⊤ ⊎ ⊤ féle Bool.

Bool' : Set
Bool' = ⊤ ⊎ ⊤

-- Nem kötelező, de egyszerűség kedvéért lehet megadni agdában
-- saját mintákat a "pattern" kulcsszó használatával.
{-
pl.
pattern trivial = tt
f : ⊤ × ⊤ → ⊤ × ⊤
f (trivial , tt) = tt , trivial

Definiálj saját mintákat, amelyeknek ⊤ ⊎ ⊤ a típusa,
az egyik neve legyen False, amely legyen az (inl tt),
a másik legyen True, amely legyen az (inr tt) a tesztek miatt.
(Nyilván nagybetűkkel, mert a kisbetűsök már foglaltak.)
-}

-- Definiáld az if_then_else'_ függvényt, amely a ⊤ ⊎ ⊤
-- típussal definiálja a Bool típust.
-- Add meg a függvény típusát is úgy, hogy a Bool'-t használja!
-- A második és harmadik paraméterek tetszőlegesek, de azonos
-- típusúaknak kell lenniük.
if_then_else'_ : {A : Set} → Bool' → A → A → A
if b then x else' y = {!   !}

if-then-else-test1 : {A : Set}{x y : A} → if (inr tt) then x else' y ≡ x
if-then-else-test1 = refl

if-then-else-test2 : {A : Set}{x y : A} → if (inl tt) then x else' y ≡ y
if-then-else-test2 = refl

-- Definiáld az alábbi logikai függvényeket, amelyek szintén Bool'-t használnak:
-- Add meg a függvények típusait is!
-- Ha a második paraméter változó, a megfelelő módon akkor is legyenek definícionális egyenlőségek.
-- Tehát a második paraméter mindig maradjon változó és úgy legyenek definiálva a függvények.
¬'_ : Bool' → Bool'
_∧'_ _∨'_ _⊃'_ : Bool' → Bool' → Bool'

¬' b = {!   !}

a ∧' b = {!   !}
a ∨' b = {!   !}
a ⊃' b = {!   !}

¬-test-1-2 : (¬' (inl tt) ≡ inr tt) × (¬' (inr tt) ≡ inl tt)
¬-test-1-2 = refl , refl

∧-test-1 : (λ a → inr tt ∧' a) ≡ (λ a → a)
∧-test-1 = refl

postulate
  funExt : ∀{i j} {A : Set i} {B : A → Set j} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

∧-test-2 : (λ a → a ∧' inl tt) ≡ (λ a → inl tt)
∧-test-2 = funExt λ { (inl tt) → refl
                    ; (inr tt) → refl}

∧-test-3 : (λ a → inl tt ∧' a) ≡ (λ a → inl tt)
∧-test-3 = refl
--------------------------------------------------
{-
Definiálj 3 értékű logikai típust 3Bool névvel datát használva!
A három értéke legyen no, undefined, yes.
-}



{-
Definiáld a 3 értékű logika műveleteit ¬3_, _∧3_, _∨3_, _⊃3_ nevekkel.
A műveletek igazságtáblái az alábbiak:
(F = false, U = undefined, T = true)
A | ¬3 A        ∧3 | F | U | T    ∨3 | F | U | T
F |   T         F  | F | F | F    F  | F | U | T
U |   U         U  | F | U | U    U  | U | U | T
T |   F         T  | F | U | T    T  | T | T | T

⊃3 | F | U | T
F  | T | T | T
U  | U | U | T
T  | F | U | T
-}

-- Add meg a függvények típusait is!

-------------------------------------------------------------------------------
-- Bizonyítsd be, hogy 3Bool izomorf a Bool ⊎ ⊤ típussal.
-- Izomorfizmus bizonyításához szükséges logikai ekvivalencia,
-- illetve az oda-vissza "járkálás" bármilyen sorrendben
-- mindig a kezdeti elemet adja vissza.

-- Használd a gyakorlaton látott átlátást segítő where blokkot,
-- illetve a to és from függvényeket is definiáld!
{- ⟵ ezt a komment kezdő jelet ki kell törölni, meg a fájl legvégén lévő zárót is, illetve ezt a szöveget is.
3↔2+1 : 3Bool ↔ Bool ⊎ ⊤
3↔2+1 = ?

-- Az alábbi lyukak mindegyikét ki lehet tölteni a C-c C-r
-- gombkombináció használatával. Ha nem lehet, akkor a fentebbi
-- logikai ekvivalencia nem helyes, mert nem izomorf.
proof₁ : snd 3↔2+1 (fst 3↔2+1 no) ≡ no
proof₁ = ?

proof₂ : snd 3↔2+1 (fst 3↔2+1 undefined) ≡ undefined
proof₂ = ?

proof₃ : snd 3↔2+1 (fst 3↔2+1 yes) ≡ yes
proof₃ = ?

proof₄ : fst 3↔2+1 (snd 3↔2+1 (inl false)) ≡ inl false
proof₄ = ?

proof₅ : fst 3↔2+1 (snd 3↔2+1 (inl true)) ≡ inl true
proof₅ = ?

proof₆ : fst 3↔2+1 (snd 3↔2+1 (inr tt)) ≡ inr tt
proof₆ = ?
ezt is ki kell törölni ezen szöveggel együtt → -}
---------------------------------------------------------
{-
Hány eleműek az alábbi típusok?
(A lib-ben is megnézhető, az ⊎, →, × mind jobbra zárójeleznek,
továbbá az operátorok erőssége csökkenő sorrendben: ×, ⊎, →)

Bool ⊎ Bool
Bool × Bool
Bool × Bool × Bool
Bool → Bool
Bool → Bool → Bool
Bool ↔ Bool
⊤ × ⊥
⊤ → ⊥
⊥ → ⊥
⊥ ↔ ⊥
(⊤ ⊎ Bool × ⊥) ↔ (Bool × ⊤)
(Bool ⊎ ⊤ × ⊥) ↔ (Bool × ⊤)
(⊤ × ⊥ × Bool ⊎ Bool ⊎ (Bool → ⊤)) → ((Bool ⊎ ⊥) × (⊤ ⊎ Bool))
-}