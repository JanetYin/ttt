module hf06 where

-- !!! WARNING !!! Valamiért iszonyat sokáig typecheck-el, kb 30-40 sec.
-- A szokásos módon orvosolható, ki kell kommentelni azokat a feladatokat, ahol a típusban van lyuk.
-- Ezt én már megcsináltam, elég csak visszakommentelni az aktuális feladatot.

open import Lib hiding (_≤ℕ_; _≥ℕ_; _≡ℕ_; reflℕ; min; max)
import Lib.Containers.List as L
open L using (List; []; _∷_)
open import Lib.Containers.Vector


even : ℕ → Bool
even 0 = true
even 1 = false
even (suc (suc n)) = even n

--------------------------------------------------------
-- Elmélet: Függőtípusok elemszámai
--------------------------------------------------------
{-
A függőtípusok is algebrai adattípusoknak számítanak, így természetesen a függőtípusok elemszámai is megadhatók könnyedén.
Nem véletlen, hogy a típusok nevei rendre Σ és Π.

Emlékeztetőül:
| A ⊎ B | = |A| + |B|
| A × B | = |A| ∙ |B|
| A → B | = |B| ^ |A|

Tfh:
P : Bool → Set
P true = Bool
P false = ⊥

Σ Bool P hány elemű lesz?
Ha a Bool-om true (1 konkrét érték), akkor Bool típusú eredményt kell a másik részbe írnom, tehát eddig 2¹ = 2
De ha a Bool-om false (1 konkrét érték), akkor ⊥ típusú eredmény kell, tehát 0¹ = 0

Tehát a nap végén | Σ Bool P | = |Bool| + |⊥| = 2, mert a P egy Bool-tól függő típust ad eredményül, tehát maga a típus vagy P true típusú értéket tartalmaz vagy P false-ot.
Az ilyen "vagy" kapcsolatról megbeszéltük korábban, hogy az az összeadást jelenti.

Legyen most:
P : Maybe Bool → Set
P nothing = ⊤
P (just true) = Bool
P (just false) = Maybe Bool → Bool

Hány elemű lesz Σ (Maybe Bool) P? Igazából a típus egyes elemei alapján csak meg kell nézni, hogy hány elemű típust adnak vissza.
| Σ (Maybe Bool) P | = | P nothing | + | P (just true) | + | P (just false) | = |⊤| + |Bool| + |Maybe Bool → Bool| = 1 + 2 + 8 = 11

Ez alapján az intuíció az lehet, hogy | Σ A B | = Σ (i : A) |B i|; tehát csak össze kell adni az egyes típusokból képzett új típusok elemszámát és ennyi.
(Nem véletlen, hogy Σ a típus neve. Ellenőrizhető, hogy A × B elemszáma könnyen ki fog jönni, hogy ha B nem függőtípus.)

Mi a helyzet, ha ugyanezt játszuk Π-vel? Hány elemű lesz Π A B?

Megint konkrét helyzetben, legyen:
P : Bool → Set
P true = Bool
P false = ⊥

| Π Bool P | =⟨ Agda szintaxissal ⟩= | (b : Bool) → P b | kell.
A függvényeknek totálisaknak kell lenniük, tehát ez azt jelenti, hogy MINDEN lehetséges b : Bool értékre P b-nek definiáltnak kell lennie, false-ra ÉS true-ra is.
Intuíció alapján | P true | ÉS | P false | kelleni fog, az ÉS kapcsolat matematikában a szorzást szokta jelenteni, tehát | P true | ∙ | P false | elemszámú lesz
ez a kifejezés.
| P true | ∙ | P false | = |Bool| ∙ |⊥| = 2 ∙ 0 = 0
Próbáljuk meg definiálni ezt a függvényt:
-}
P₁ : Bool → Set
P₁ true = Bool
P₁ false = ⊥

ΠBoolP : Π Bool P₁
ΠBoolP b = {!!}
-- Rájöhetünk, hogy a false ággal gondok lesznek.
{-
Következő példa, ez a P már ismerős:
P : Maybe Bool → Set
P nothing = ⊤
P (just true) = Bool
P (just false) = Maybe Bool → Bool

Hány elemű lesz Π (Maybe Bool) P?
A függvények továbbra is totálisak kell legyenek. Ez azt jelenti, hogy a függvény definiálva kell legyen (P nothing)-ra, (P (just true))-ra ÉS (P (just false))-ra is,
tehát lesz | P nothing | ∙ | P (just true) | ∙ | P (just false) | elemünk, |⊤| ∙ |Bool| ∙ |Maybe Bool → Bool| = 1 ∙ 2 ∙ 2³ = 16 elemű lesz Π (Maybe Bool) P.

Intuíció alapján általánosan | Π A B | = Π (i : A) | B i |, tehát csak az összes B-ből képezhető típus elemszámát össze kell szorozni.

Gyakorlás:
Adott a következő P:

P : Bool × Bool → Set
P (true , true) = ⊤
P (true , false) = Bool
P (false , true) = Bool → Bool ⊎ ⊤
P (false , false) = Bool ⊎ ⊤ → Bool

Hány elemű lesz Σ (Bool × Bool) P?
Hány elemű lesz Π (Bool × Bool) P?

Kicsit érdekesebb ezeket vegyíteni, de az elv ugyanaz marad.
Marad ugyanaz a P.

Hány elemű lesz Π (a : Bool) (Σ (b : Bool) (P (a , b)))? ( Agda szintaxissal (a : Bool) → Σ Bool (λ b → P (a , b)) )
Hány elemű lesz Σ (a : Bool) (Π (b : Bool) (P (a , b)))? ( Agda szintaxissal Σ Bool λ a → (b : Bool) →  P (a , b)) )
-}
--------------------------------------------------------

{-
Definiáld a _≤_ és _≥_ függvényeket, amelyek rendre meghatározzák
típusszinten, hogy az első szám kisebbegyenlő, illetve nagyobbegyenlő,
mint a másik szám.
-}
infix 4 _≤ℕ_
_≤ℕ_ : ℕ → ℕ → Set
_≤ℕ_ = {!   !}

≤-test1 : (λ x → 0 ≤ℕ x) ≡ (λ x → ⊤)
≤-test1 = refl

≤-test2 : 3 ≤ℕ 10
≤-test2 = tt

≤-test3 : ¬ (10 ≤ℕ 3)
≤-test3 ()

infix 4 _≥ℕ_
_≥ℕ_ : ℕ → ℕ → Set
_≥ℕ_ = {!   !}

≥-test1 : (λ x → x ≥ℕ 0) ≡ (λ x → ⊤)
≥-test1 = refl

≥-test2 : 30 ≥ℕ 10
≥-test2 = tt

≥-test3 : ¬ (10 ≥ℕ 30)
≥-test3 ()

{-
Definiáld a _≡ℕ_ függvényt, amely típusszinten meghatározza, hogy
két természetes szám egyenlő egymással.
-}
infix 4 _≡ℕ_
_≡ℕ_ : ℕ → ℕ → Set
_≡ℕ_ = {!   !}

≡ℕ-test1 : 3 ≡ℕ 3
≡ℕ-test1 = tt

≡ℕ-test2 : ¬ (3 ≡ℕ 4)
≡ℕ-test2 ()

≡ℕ-test3 : (4 ≡ℕ 3) ≡ ⊥
≡ℕ-test3 = refl

{-
Bizonyítsd, hogy az ≡ℕ művelet reflexív!
Segítség: Nézd meg, hogy mi történik, ha mintaillesztés történik n-re. (Nem mintha lehetne igazán mást csinálni.)
-}
reflℕ : (n : ℕ) → n ≡ℕ n
reflℕ = {!   !}

{-
Definiáld a min és a max függvényt, amely két szám közül rendre a kisebbet, illetve
a nagyobbat adja vissza és mellette egy bizonyítást, hogy a jót adja vissza.
A függőtípusokkal egy teljes specifikációját le lehet írni a függvénynek,
ez van most a min és a max függvényekben megadva.
Olvasva a következő a specifikáció:
Előfeltétel: Van két tetszőleges ℕ számom.
Utófeltétel: Létezik olyan (n : ℕ) szám (Σ első paramétere), amelyre teljesül, hogy (Σ második paramétere):
  -- ha x ≤ y, akkor x megegyezik n-nel
  VAGY
  -- ha x ≥ y, akkor y megegyezik n-nel
-}
min : (x y : ℕ) → Σ ℕ (λ n → x ≤ℕ y × x ≡ℕ n ⊎ x ≥ℕ y × y ≡ℕ n)
min = {!   !}

min-test1 : fst (min 3 6) ≡ 3
min-test1 = refl

min-test2 : fst (min 6 4) ≡ 4
min-test2 = refl

min-test3 : fst (min 5 5) ≡ 5
min-test3 = refl

max : (x y : ℕ) → Σ ℕ (λ n → x ≥ℕ y × x ≡ℕ n ⊎ x ≤ℕ y × y ≡ℕ n)
max = {!   !}

max-test1 : fst (max 3 6) ≡ 6
max-test1 = refl

max-test2 : fst (max 6 4) ≡ 6
max-test2 = refl

max-test3 : fst (max 5 5) ≡ 5
max-test3 = refl

--------------------------------------------------------------------

-- Definiáld a programozás elmélet tárgyról ismert χ (\Gc) függvényt, amely Bool-t számra alakít, true-t 1-re, false-ot 0-ra.
χ : Bool → ℕ
χ = {!!}

_ : χ true ≡ 1
_ = refl

_ : χ false ≡ 0
_ = refl

{-
Definiáljuk az órán emlegetett pontosabb filtert.
Szükség van hozzá egy count függvényre, ami megszámolja, hogy hány elemre igaz egy predikátum.
-}
count : ∀{i}{A : Set i}{n : ℕ} → (A → Bool) → Vec A n → ℕ
count = {!!}

_ : count even (1 ∷ []) ≡ 0
_ = refl

_ : count even (3 ∷ 2 ∷ 4 ∷ 5 ∷ 112 ∷ []) ≡ 3
_ = refl

_ : count (_<ᵇ 10) (0 ∷ 7 ∷ 3 ∷ []) ≡ 3
_ = refl

_ : count (_<ᵇ 10) (0 ∷ 71 ∷ 3 ∷ 34 ∷ 5 ∷ 10 ∷ 10 ∷ 9 ∷ 8 ∷ []) ≡ 5
_ = refl

_ : count (9 <ᵇ_) (0 ∷ 71 ∷ 3 ∷ 34 ∷ 5 ∷ 10 ∷ 10 ∷ 9 ∷ 8 ∷ []) ≡ 4
_ = refl

-- Add meg a filter típusát helyesen:
-- (A paraméterek helyesek, de lehet, hogy kell velük mást is csinálni)
filter : ∀{i}{A : Set i}{n : ℕ} → (A → Bool) → Vec A n → Vec A {!!}
filter = {!!}

_ : filter even (1 ∷ []) ≡ []
_ = refl

_ : filter even (3 ∷ 2 ∷ 4 ∷ 5 ∷ 112 ∷ []) ≡ 2 ∷ 4 ∷ 112 ∷ []
_ = refl

_ : filter (_<ᵇ 10) (0 ∷ 7 ∷ 3 ∷ []) ≡ 0 ∷ 7 ∷ 3 ∷ []
_ = refl

_ : filter (_<ᵇ 10) (0 ∷ 71 ∷ 3 ∷ 34 ∷ 5 ∷ 10 ∷ 10 ∷ 9 ∷ 8 ∷ []) ≡ 0 ∷ 3 ∷ 5 ∷ 9 ∷ 8 ∷ []
_ = refl

_ : filter (9 <ᵇ_) (0 ∷ 71 ∷ 3 ∷ 34 ∷ 5 ∷ 10 ∷ 10 ∷ 9 ∷ 8 ∷ []) ≡ 71 ∷ 34 ∷ 10 ∷ 10 ∷ []
_ = refl

{-
Definiáld a takeWhile függvényt, amely addig tartja meg egy vektor elemeit,
amíg a feltétel teljesül. Az eredmény egy rendezett pár, ahol az első komponens egy szám, hogy hány elemet sikerült vennünk az elejéről.
A második pedig maguk az elemek.
Megj.: Ez a függvény hasonlóan megírható jobban, mint a filter.
-}
takeWhile : ∀{i}{A : Set i}{n : ℕ} → (A → Bool) → Vec A n → Σ ℕ (λ k → Vec A k)
takeWhile = {!   !}

takeWhile-test1 : takeWhile even (2 ∷ 4 ∷ 0 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (3 , 2 ∷ 4 ∷ 0 ∷ [])
takeWhile-test1 = refl

takeWhile-test2 : takeWhile even (1 ∷ 2 ∷ 3 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (0 , [])
takeWhile-test2 = refl

takeWhile-test3 : takeWhile (0 <ᵇ_) (1 ∷ 2 ∷ 3 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (6 , 1 ∷ 2 ∷ 3 ∷ 3 ∷ 4 ∷ 5 ∷ [])
takeWhile-test3 = refl

takeWhile-test4 : takeWhile (0 <ᵇ_) (0 ∷ 1 ∷ 2 ∷ 4 ∷ 5 ∷ []) ≡ (0 , [])
takeWhile-test4 = refl

{-
Egészítsd ki a takeWhile definícióját egy bizonyítással, amely azt mondja,
hogy az eredmény elemszáma legfeljebb n.
-}

takeWhile' : ∀{i}{A : Set i}{n : ℕ} → (A → Bool) → Vec A n → Σ ℕ (λ x → Vec A x × x ≤ℕ n)
takeWhile' = {!   !}

takeWhile'-test1 : takeWhile' even (2 ∷ 4 ∷ 0 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (3 , 2 ∷ 4 ∷ 0 ∷ [] , tt)
takeWhile'-test1 = refl

takeWhile'-test2 : takeWhile' even (1 ∷ 2 ∷ 3 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (0 , [] , tt)
takeWhile'-test2 = refl

takeWhile'-test3 : takeWhile' (0 <ᵇ_) (1 ∷ 2 ∷ 3 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (6 , 1 ∷ 2 ∷ 3 ∷ 3 ∷ 4 ∷ 5 ∷ [] , tt)
takeWhile'-test3 = refl

takeWhile'-test4 : takeWhile' (0 <ᵇ_) (0 ∷ 1 ∷ 2 ∷ 4 ∷ 5 ∷ []) ≡ (0 , [] , tt)
takeWhile'-test4 = refl

{-
Definiáld a span függvényt, amely egy vektort két részre bont azon a ponton, ahol
egy adott tulajdonság már nem teljesül.
-}
span : ∀{i}{A : Set i}{n : ℕ} → (p : A → Bool) → Vec A n → Σ ℕ (λ x → Σ ℕ (λ y → Vec A x × Vec A y × x + y ≡ℕ n))
span = {!   !}

span-test1 : span even (2 ∷ 4 ∷ 1 ∷ []) ≡ (2 , 1 , 2 ∷ 4 ∷ [] , 1 ∷ [] , tt)
span-test1 = refl

span-test2 : span (_<ᵇ 3) (2 ∷ 4 ∷ 1 ∷ []) ≡ (1 , 2 , 2 ∷ [] , 4 ∷ 1 ∷ [] , tt)
span-test2 = refl

span-test3 : span {_} {ℕ} (λ _ → false) (2 ∷ 4 ∷ 1 ∷ []) ≡ (0 , 3 , [] , 2 ∷ 4 ∷ 1 ∷ [] , tt)
span-test3 = refl

span-test4 : span {_} {ℕ} (λ _ → true) (2 ∷ 4 ∷ 1 ∷ []) ≡ (3 , 0 , 2 ∷ 4 ∷ 1 ∷ [] , [] , tt)
span-test4 = refl

-- Így nehéz feladat:
-- Definiáld a splitOn függvényt, amely egy adott tulajdonságú elem mentén feldarabolja a listát.
{-
splitOn : ∀{i}{A : Set i}{n}(p : A → Bool) → Vec A n → {!!}
splitOn = {!!}

_ : let k = splitOn even (1 ∷ 2 ∷ 3 ∷ []) in k ≡ (2 , (1 ∷ []) ∷ (3 ∷ []) ∷ [])
_ = refl

_ : let k = splitOn even (2 ∷ []) in k ≡ (2 , [] ∷ [] ∷ [])
_ = refl

_ : let k = splitOn even (4 ∷ 2 ∷ []) in k ≡ (3 , [] ∷ [] ∷ [] ∷ [])
_ = refl

_ : let k = splitOn even (3 ∷ 1 ∷ []) in k ≡ (1 , (3 ∷ 1 ∷ []) ∷ [])
_ = refl

_ : let k = splitOn even (12 ∷ 9 ∷ 5 ∷ 7 ∷ 1 ∷ 2 ∷ 5 ∷ 11 ∷ 4 ∷ []) in k ≡ (4 , [] ∷ (9 ∷ 5 ∷ 7 ∷ 1 ∷ []) ∷ (5 ∷ 11 ∷ []) ∷ [] ∷ [])
_ = refl
-}

-- Így egyszerűbb:
-- splitOn is megadható a count-tal:
{-
splitOn' : ∀{i}{A : Set i}{n}(p : A → Bool)(xs : Vec A n) → Vec (List A) {!!}
splitOn' = {!!}

_ : let k = splitOn' even (1 ∷ 2 ∷ 3 ∷ []) in k ≡ (1 ∷ []) ∷ (3 ∷ []) ∷ []
_ = refl

_ : let k = splitOn' even (2 ∷ []) in k ≡ [] ∷ [] ∷ []
_ = refl

_ : let k = splitOn' even (4 ∷ 2 ∷ []) in k ≡ [] ∷ [] ∷ [] ∷ []
_ = refl

_ : let k = splitOn' even (3 ∷ 1 ∷ []) in k ≡ (3 ∷ 1 ∷ []) ∷ []
_ = refl

_ : let k = splitOn' even (12 ∷ 9 ∷ 5 ∷ 7 ∷ 1 ∷ 2 ∷ 5 ∷ 11 ∷ 4 ∷ []) in k ≡ [] ∷ (9 ∷ 5 ∷ 7 ∷ 1 ∷ []) ∷ (5 ∷ 11 ∷ []) ∷ [] ∷ []
_ = refl
-}

-- Definiáld a partition függvényt, amely egy vektor elemeit szétválogatja egy adott tuladonság alapján.
-- Az eredmény egy rendezett 4-es legyen, amely első két komponense
-- a két szétvágott Vec elemszámai legyenek az első szám legyen annyi, ahány elemre teljesült a tulajdonság,
-- a másik szám pedig legyen annyi, amennyire nem teljesült.
-- A másik két komponens legyen a két vektor, a harmadik helyen azon elemek, amelyekre teljesült a tulajdonság,
-- a negyedik helyen pedig azon elemek legyenek, amelyekre nem teljesült.
{-
partition : ∀{i}{A : Set i}{n}(p : A → Bool)(xs : Vec A n) → {!!}
partition = {!!}

_ : let k = partition even (1 ∷ 2 ∷ 3 ∷ []) in k ≡ (1 , 2 , 2 ∷ [] , 1 ∷ 3 ∷ [])
_ = refl

_ : let k = partition (_<ᵇ 10) (10 ∷ 11 ∷ 0 ∷ 9 ∷ 10 ∷ 6 ∷ 5 ∷ []) in k ≡ (4 , 3 , 0 ∷ 9 ∷ 6 ∷ 5 ∷ [] , 10 ∷ 11 ∷ 10 ∷ [])
_ = refl

_ : let k = partition (_<ᵇ 5) (10 ∷ 11 ∷ 0 ∷ 9 ∷ 10 ∷ 6 ∷ 5 ∷ []) in k ≡ (1 , 6 , 0 ∷ [] , 10 ∷ 11 ∷ 9 ∷ 10 ∷ 6 ∷ 5 ∷ [])
_ = refl

_ : let k = partition even (8 ∷ 4 ∷ 6 ∷ 12 ∷ 14 ∷ 32 ∷ []) in k ≡ (6 , 0 , 8 ∷ 4 ∷ 6 ∷ 12 ∷ 14 ∷ 32 ∷ [] , [])
_ = refl

_ : let k = λ p → partition {A = ℕ} p [] in k ≡ λ p → 0 , 0 , [] , []
_ = refl
-}

-- Definiáld a partitionWith függvényt, amely a függvény eredménye alapján dönti el, hogy melyik vektorba teszi a függvény által átalakított értéket.
{-
partitionWith : ∀{i j k}{A : Set i}{B : Set j}{C : Set k}{n} → (A → B ⊎ C) → Vec A n → {!!}
partitionWith = {!!}

_ : let k = partitionWith (λ n → if even n then inl n else inr n) (1 ∷ 2 ∷ 3 ∷ []) in k ≡ (1 , 2 , 2 ∷ [] , 1 ∷ 3 ∷ [])
_ = refl

_ : let k = partitionWith (λ n → if n <ᵇ 10 then inl n else inr n) (10 ∷ 11 ∷ 0 ∷ 9 ∷ 10 ∷ 6 ∷ 5 ∷ []) in k ≡ (4 , 3 , 0 ∷ 9 ∷ 6 ∷ 5 ∷ [] , 10 ∷ 11 ∷ 10 ∷ [])
_ = refl

_ : let k = partitionWith (λ n → if n <ᵇ 5 then inl n else inr n) (10 ∷ 11 ∷ 0 ∷ 9 ∷ 10 ∷ 6 ∷ 5 ∷ []) in k ≡ (1 , 6 , 0 ∷ [] , 10 ∷ 11 ∷ 9 ∷ 10 ∷ 6 ∷ 5 ∷ [])
_ = refl

_ : let k = partitionWith (λ n → if even n then inl n else inr n) (8 ∷ 4 ∷ 6 ∷ 12 ∷ 14 ∷ 32 ∷ []) in k ≡ (6 , 0 , 8 ∷ 4 ∷ 6 ∷ 12 ∷ 14 ∷ 32 ∷ [] , [])
_ = refl

_ : let k = λ p → partitionWith {A = ℕ} {ℕ} {ℕ} p [] in k ≡ λ p → 0 , 0 , [] , []
_ = refl
-}

-- Bizonyítsd be az alábbi állítást:
ΣΣ=Σ× : ∀{i j k}{A : Set i}{B : Set j}(P : A → B → Set k) → (Σ A (λ a → Σ B (λ b → P a b))) ↔ (Σ (A × B) (λ (a , b) → P a b))
ΣΣ=Σ× P = {!   !}

-- Definiáld a _<ℕ∞_ függvényt, amely egy természetes számot és egy
-- kotermészetes számot összehasonlít, megvizsgálja, hogy a természetes szám
-- kisebb-e, mint a kotermészetes.
infix 4 _<ℕ∞_
_<ℕ∞_ : ℕ → ℕ∞ → Set
n <ℕ∞ k = {!!}

<ℕ∞-test1 : (9 <ℕ∞ 10) ≡ ⊤
<ℕ∞-test1 = refl
<ℕ∞-test2 : (9 <ℕ∞ 9) ≡ ⊥
<ℕ∞-test2 = refl
<ℕ∞-test3 : (9 <ℕ∞ 8) ≡ ⊥
<ℕ∞-test3 = refl
<ℕ∞-test4 : (9 <ℕ∞ 11) ≡ ⊤
<ℕ∞-test4 = refl
<ℕ∞-test5 : (λ x → x <ℕ∞ 0) ≡ (λ x → ⊥)
<ℕ∞-test5 = refl

-- NEHÉZ LEHET: Ha az előző jól van megcsinálva, akkor ez triviális.
-- Bizonyítsd be, hogy ∀ n : ℕ-re n <ℕ∞ ∞
n<∞ : ∀ n → n <ℕ∞ ∞
n<∞ = {!!}
