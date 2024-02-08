open import LibTypes hiding ( _⊎_ ; _↔_) -- lib csak típusokkal
open import Lib.Containers.List.Type

-- Véges típusosok
-- Haskelles data deklaráció
-- data <Típusnév> = <Konstruktor> | ...

{-

data <Típusnév> : Set where
  <Konstruktor1> : <Típus>
  <Konstruktor2> : <Típus>
  .
  .
  .

-}

-- data (,) a b = (,) a b ≡ rendezett pár
-- (1,2) stb

-- data _×_ (A : Set)(B : Set) : Set where
--  _,_ : A → B → A × B

-- data Either a b = Left a | Right b

data _⊎_ (A : Set)(B : Set) : Set where
  inl : A → A ⊎ B -- KONSTRUKTOR = egy absztrakt függvény ami egy típus elemét építi fel
  inr : B → A ⊎ B

-- konstruktorok nem kiszámíthatóak
-- annak nincs értéke hogy inl 1
-- cserébe meg tudod viszgálni melyik konstruktort veszi fel

-- DESTRUKTOR (REKURZOR, ITERÁTOR, ELIMINÁTOR, CATAMORPHISM)
-- A típusnak a destruktora az úgy néz ki hogy:
-- cataA : {C : Set} → A → ????? sötét mágia → C

-- Pl.:
-- Bool-nak a destruktora az if-then-else

-- "sőtét mágia" ≡ a két C típusú paraméterrel
if_then_else : {C : Set} → Bool → C → C → C
if false then c₁ else c₂ = c₂
if true then c₁ else c₂ = c₁

-- Destruktor = a mintaillesztést "szimulálja"

-- Pl 2.:
-- A ⊎ B-nek a destruktora a case függvény
case : {C : Set}{A B : Set} → A ⊎ B → (A → C) → (B → C) → C
-- pl C#-ba C Case(Either<A,B> either, Func<A,C> f1, Func<B,C> f2)
case (inl a) A→C B→C = A→C a
case (inr b) A→C B→C = B→C b

{-

case :
 {C : Set}{A B : Set} -- Ezek implicit paraméterek ⇒ a paraméterek nem jelennek
                         meg automatikusan az egyenlőség bal oldalán. ÉS ha egy függvény
 →                       implicit paramétert vár azt az Agda kitalálja a kontextusból
                         {A B : Set} ≡ {A : Set}{B : Set}
 A ⊎ B                -- sima explicit paraméter
 →
 (A → C)              -- magasabbrendű rendű explicit paraméter ≡ ez egy függvény
 →
 (B → C)
 →
 C                    -- Utolsó nyíl után a visszatérési érték típusa
-}

-- if b then true else false ≡ b
-- case k inl inr ≡ k

_↔_ : Set → Set → Set -- típus alias vagy szinoníma
A ↔ B = (A → B) × (B → A)

id : {A : Set} → A ↔ A -- C-c C-r a refine
id = (λ x → x) , λ x → x -- C-c C-, hole-ok típus

-- C-c C-n
-- Bool ↔ ℕ
-- ≡
-- (Bool → ℕ) × (ℕ → Bool)

-- Bijekció: ha van egy f : A → B függvényünk, akkor f bijekció ha
-- f injektív azaz ∀ a,b esetén f(a) ≡ f(b) ⊃ a ≡ b
-- f szürjektív azaz ∀ b esetén ∃ a hogy f(a) ≡ b
-- f és g : B → A bijektívek ha ∀ a esetén f(g(a)) ≡ a és ∀ b esetén g(f(b)) ≡ b
-- itt f⁻¹ ≡ g
-- Ez a ↔ csak bizonyítás nélkül

-- Mintaillesztés: A bemenetet felbontja → konstruktora bontja fel (lehet 1 konstruktor)
-- Comintaillesztés: A kimenetet felbontja → a konstruktor paramétereire bontja fel (pontosan 1 konstruktor)
-- C-c C-c ENTER, ha az eredmény típusának 1 konstruktora van.
-- _×_ az oké, mert 1 konstruktora van (_,_) aminek két paramétere van fst és snd

-- Ha hole-ba A → B típusú kifejezés kell, akkor C-c C-c ENTER felveszi az = bal oldalára a paramétereket
comm⊎ : {A B : Set} → (A ⊎ B) ↔ (B ⊎ A)
fst comm⊎ (inl x) = inr x
fst comm⊎ (inr x) = inl x
snd comm⊎ (inl x) = inr x
snd comm⊎ (inr x) = inl x

-- C-c C-a = a magic megoldó bill kombináció => valami típushelyeset belerak a holeba

-- STRUKTURÁLIS INDUKCIÓ
-- 1,2,3 stb

-- one : ℕ
-- one = 1

-- Hogyan vannak definiálva?
-- Anno matalap: Teljes Indukció
-- P tulajdonságunk
-- P(0) igaz (kezdeti vagy "termináló" eset)
-- Ha tudjuk hogy P(n) igaz (indukciós hipotézis) akkor P(n + 1)
-- Így tudtuk megmondani hogy valami minden ℕ-re igaz

-- Ezzel definiálunk ℕ-ot

--data ℕ : Set where
--  zero : ℕ -- termináló eset
--  suc  : ℕ → ℕ -- ha tudjuk egy n : ℕ-ről hogy definiálva van (indukciós hipotézis) akkor n+1 is definiálva van

-- n+1-ben a + még technically létezik, mi ezt csak így "interpretáljuk"

-- Mi felel meg egy természetes számnak?
-- Az hogy mennyi suc van egy zero-n reprezentálja mennyi a szám értéke

zero' : ℕ
zero' = zero -- 0db suc

one' : ℕ
one' = suc zero -- 1db suc

five' : ℕ
five' = suc (suc (suc (suc (suc zero)))) -- 5db suc

five'' : ℕ
five'' = 5 -- UGYANAZ mint five' csak szintaktikus cukorka


-- írjunk pár fv-t
-- double, az duplázza meg a számot
double : ℕ → ℕ -- mi minden fv-t ilyen teljes indukció style-ba fogjuk írni
double zero = zero
-- kezdeti eset: 0 * 2 ≡ ? (itt a * 2 nem létezik csak mennyinek kéne lennie ha pl létezne)
double (suc n) = suc (suc (double n))
-- rekzurív hívás, ahol majd alkalmazzuk az indukciós hipotézistű
-- egy suc-ot rárakunk egy ℕ típusú kifejezésre
-- az olyan "mintha" megnövelnék 1-el
-- (1 + n) * 2 ≡ ?
-- Van egy indukciós hipotézisünk, ami azt mondja, hogy tudjuk mennyi n * 2
-- (1 + n) * 2 ≡ 2 + n * 2 ≡ 1 + (1 + n * 2) ⇒ suc (suc (double n))
-- reinterpretáljuk az 1+-t suc-á

-- 1-nek a fele legyen 0, tehát lényegében floor(x/2)
half : ℕ → ℕ
-- 0 / 2 ≡ ?
half zero = zero
-- (n + 1) / 2 ≡ ?
-- tudjuk mennyi n / 2
-- (n + 1) / 2 ≡ n / 2 + 1 / 2 <- yikes
-- bevezetünk egy másodlagos termináló esetet
-- 1 / 2 = ? -> megadtuk hogy 0
half (suc zero) = zero
-- (n + 2) / 2 ≡ n / 2 + 1
half (suc (suc x)) = suc (half x)

_+_ : ℕ → ℕ → ℕ -- játszuk indukciós hipotézist :D
-- 0 + k ≡ ? ≡ k
zero + k = k
-- indukciós hipotézis: n + k
-- (1 '+' n) + k ≡ ? asszociativitást ≡ 1 '+' (n + k)
suc n + k = suc (n + k)

-- unit test
t1 : 5 + 3 ≡ 8
t1 = refl

_*_ : ℕ → ℕ → ℕ -- játszunk megint
-- 0 * k ≡ ? ≡ 0
zero * k = zero
-- indukciós hipotézis: n * k
-- (n + 1) * k ≡ ? disztributivitás ≡ n * k + k
-- már van összeadás
suc n * k = (n * k) + k

min : ℕ → ℕ → ℕ
-- három termináló eset lesz ⇒ három eredmény "lehetséges"
-- min(0,0) ≡ 0
min zero zero = zero
-- min(0, 1 + k) ≡ 0
min zero (suc k) = zero
-- min(1 + k, 0) ≡ 0
min (suc n) zero = zero
-- indukciós hipotézis: min(n,k)
-- min(1 + n, 1 + k) ≡ 1 + min(n,k)
min (suc n) (suc k) = suc (min n k)


-- Back in véges típusok
-- Iterátor: egy típuson "elágaz"
-- Mi ℕ iterátora?
-- emlékezhetsz arra, hogy az iterátoroknál minden paraméter az egyik konstruktornak a megfelelője
-- akkor kell egy paraméter a 0-nak
-- kell egy paraméter a sucnak

{-
Megnézzük a konstruktorokat
  zero : ℕ
  suc : ℕ → ℕ
Ha egy Q típus felett írunk iterátort, minden Q-t lecserélünk C-re
  zero-nak a paramétere : C
  suc-nak a paramétere : C → C
-}

iteℕ : {C : Set} → ℕ → C → (C → C) → C
iteℕ zero czero csuc = czero
iteℕ (suc x) czero csuc = csuc (iteℕ x czero csuc)

-- "Rekurzor" <= gonosz dolog
-- recℕ : {C : Set} → ℕ → C → (ℕ → C → C) → C

{-
data List (A : Set) : Set where
  [] : List A                     | []
  _∷_ : A → List A → List A       | :
∷ = vscodeban  ű:: emacsban \::
-}

sum : List ℕ → ℕ -- itt is indukciós hipotézist fogunk játszani
-- termináló eset
-- Σ ∅ ≡ ? ≡ 0
sum [] = zero
-- indukciós hipotézis
-- Σ xs tudjuk mennyi
-- Σ ({x} ∪ xs) ≡ ? ebben az esetben ≡ x + Σ xs
sum (x ∷ xs) = x + sum xs

product : List ℕ → ℕ -- pl product [1,2,4] ≡ 8
-- ha azt mondjuk Π {} ≡ 0 → Π {x} ≡ Π {} * Π {x} ≡ 0 * Π {x}
-- ilyen esetekben általában a művelet egységelemére gondolunk
-- azaz melyik az a k hogy k * x ≡ x
product [] = 1
-- indukciós hipotézis
-- Π xs mennyi
product (x ∷ xs) = x * product xs

-- lista hossza
length : {A : Set} → List A → ℕ
length [] = zero
-- indukciós hipotézis
-- tujduk hogy |xs| mennyi
-- |{x} ∪ xs| ≡ ?
length (x ∷ xs) = suc (length xs)

-- itt annyira nem mindegy melyik paraméteren végezzük az indukciós hipotézist
_++_ : {A : Set} → List A → List A → List A
-- termináló eset: [] ++ xs ≡ ?
[] ++ ys = ys
-- indukciós hipotézis:
-- tudjuk xs ++ ys mennyi
(x ∷ xs) ++ ys = xs ++ (x ∷ ys)
-- Alapból, ez jó
-- "pakolgatós módszer"
-- De bizonyítani nem kellemes vele
-- Alternatíva x ∷ (xs ++ ys)
-- (suc x) + y ≡ suc (x + y)

-- Lista iterátora
{-

  [] : List A
  _∷_ : A → List A → List A

1, minden List A-t lecserélünk C-re

  [] paramétere : C
  _∷_ paramétere : A → C → C
-}
iteList : {C : Set}{A : Set} → List A → C → (A → C → C) → C
iteList [] c[] c∷ = c[]
iteList (x ∷ xs) c[] c∷ = c∷ x (iteList xs c[] c∷)
-- fun fact, ez haskellből a foldr
-- Ugye iteList k [] _∷_ ≡ k
