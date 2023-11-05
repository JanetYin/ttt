open import Lib hiding (Fin ; _+_ ; Σ)

-- FÜGGŐ TÍPUSOK: Egy típus ami egy értéktől függ
-- 0 : ℕ
-- 1 : ℕ
-- true : Bool
-- false : Bool
-- ℕ : Set
-- Bool : Set
-- ⊤ : Set

-- true : Bool
-- Bool : Set (Set ≡ Set₀) <-- itt megállunk
-- Set₀ : Set₁
-- Set₁ : Set₂

--       V tetszőleges A típus esetén
-- id : {A : Set} → A → A
--           ^ megmondtuk az 'A' egy típus

f : Bool → Set
f false = ⊤
f true = Bool

-- értékeket fel tudunk emelni típusszintre, azaz függvényparamétereket felhasználunk a típusban
--  V Bool típusú paraméter amit elneveztem b-nek (Bool → ...)
g : (b : Bool) → f b
---  ^ explicit paraméter = olyan paraméter ami az = jobb oldalán megjelenik ÉS mindig fvhíváskor meg kell adni
g false = tt
g true = false

-- implicit paraméter = nem mindig jelenik meg a jobb oldalt és az agda kitalálja magától a kontextusból
--                  V explicit A típusú paraméter
-- id : {A : Set} → A → A
--      ^ implicit típus-típusú paraméter

-- TECHNOLÓGIA #1 - predikátumok
-- egy fv akkor predikátum ha a típusa az ... → Set (még azt szokás megkötni hogy ... nem Set)

-- logikai függvények = predikátumok
-- pl.: isDivisibleBy2


half : ℕ → ℕ
half zero = zero
half (suc zero) = zero -- mi 1-nek a fele?
-- A, ez nincs értelmezve
-- B, legyen pl 0
half (suc (suc x)) = suc (half x)

isDivisibleBy2 : ℕ → Set -- Bool helyett Set-be képzünk
-- az igaz állításokat egy triviális típusal szokás kódolni - ⊤
-- a hamis állításokat egy olyan típussal szokás kódolni aminek nincs eleme - ⊥
isDivisibleBy2 zero = ⊤
isDivisibleBy2 (suc zero) = ⊥
isDivisibleBy2 (suc (suc x)) = isDivisibleBy2 x

--                   V ha az n páratlan akkor ez a paraméter ⊥ típusú lesz, olyan kifejezést meg nem lehet előállítani
goodHalf : (n : ℕ) → isDivisibleBy2 n → ℕ
--                    ^ proof paraméter
goodHalf zero proof = zero
-- lenyelni a suc zero esetet
goodHalf (suc zero) ()
goodHalf (suc (suc n)) proof = goodHalf n proof

-- FÜGGŐTÍPUSOS DATÁKAT
-- emléxünk volt a lista
{-
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A
-}

-- turbózzuk fel egy kicsit
-- A vektor lesz egy lista ami A TÍPUSBAN ELTÁROLJA A (LISTA) HOSSZÁT
-- A vektor a hossza által van indexelve
-- A vektor egy ℕ-ból képző típucsalád
--                   |
--                   V
data Vec (A : Set) : ℕ → Set where
  [] : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

infixr 5 _∷_

-- írjunk pl map függvényt
-- pl listánál "map f xs = []"

--                                                   V nagy erős megkötés
map : {A B : Set}{n : ℕ} → (A → B) → Vec A n → Vec B n
map f [] = [] -- ha itt üres listára ill mintát, akkor tudjuk hogy n = 0 ⇒ az eredmény vektor hossza is 0
map f (x ∷ vs) = f x ∷ map f vs

-- filozófiai kérdés:
-- mik a paraméterek és az eredmény hossza(i)?
-- Rossz hozzáállás: Vec A n → Vec B k → Vec (A × B) (min n k)
-- Jó hozzállás: Vec A n → Vec B n → Vec (A × B) n
zip : {A B : Set}{n : ℕ} → Vec A n → Vec B n → Vec (A × B) n
zip [] [] = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip xs ys
-- C-c C-a = Auto
-- automatikusan berak vmi típushelyeset a lyukba

_+_ : ℕ → ℕ → ℕ
zero + k = k
suc n + k = suc (n + k)
-- (1 + n) + k = ? (indhipo = n + k)
-- itt az egyenlőségek ún DEFINÍCIONÁLIS EGYENLŐSÉGEK
-- ∀k. zero + k = k
-- ∀n k. suc n + k = suc (n + k)
-- BIZONYÍTHATÓ EGYENLŐSÉG
-- ∀k. k + zero = k  <=> nem definícionális
-- k + n ≝ n + k => akkor ezeket az egyenlőségeket végtelenszer tudná alkalmazni => végtelen loopba kerülne

-- C-c C-c <paraméterek> = mintaillesztés
_++_ : {A : Set}{n k : ℕ} → Vec A n → Vec A k → Vec A (n + k)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- indexelés
-- Mikor nincs az indexelés definiálva?
-- _!!_ : List A → ℕ → A
-- n < 0 akkor nem, de ez meg van oldva
-- n >= a lista hossza
-- [1,2,3] !! 3 ilyen nincs

_<_ : ℕ → ℕ → Set
zero < zero = ⊥
zero < suc k = ⊤
suc n < zero = ⊥
suc n < suc k = n < k -- (1 + n) < (1 + k) ↔ n < k

_!!_ : {A : Set}{n : ℕ} → Vec A n → (k : ℕ) → (k < n) → A
([] !! zero) ()
([] !! suc k) ()
((x ∷ xs) !! zero) proof = x
((x ∷ xs) !! suc k) proof = (xs !! k) proof

_<'_ :  ℕ → ℕ → Set
n <' zero = ⊥
zero <' suc k = ⊤
suc n <' suc k = n <' k

_!!'_ : {A : Set}{n : ℕ} → Vec A n → (k : ℕ) → (k <' n) → A
((x ∷ xs) !!' zero) proof = x
((x ∷ xs) !!' suc k) proof = (xs !!' k) proof

-- Chapter #2 - lelki fájdalom
-- FIN mint típuscsalád
-- Fin egy ℕ által indexelt típucsalád
-- Fin : ℕ → Set

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc : {n : ℕ} → Fin n → Fin (suc n)

{-
Fin n = n-nél kisebb számok "halmaza"
Fin a finite rövidítése
0 "∈" Fin 1, Fin 2, Fin 3, stb
1 "∈" Fin 2, Fin 3, Fin 4, stb

 n |   Fin n elemei
   | fzero | fsuc
-------------------
 0 |       |
 1 | 0     |
 2 | 0     | 1
 3 | 0     | 1 2

fsuc : Fin n → Fin (n + 1)
Fin (n + 1) ≡ { 0 } ∪ { x + 1 | x ∈ Fin n }
-}

f0 : Fin 0 → ⊥
f0 ()
-- Fin 0 ↔ ⊥

-- |Fin k| = k

f1 : Fin 1
f1 = fzero

f2 f2' : Fin 2
f2 = fzero
f2' = fsuc fzero

_!!''_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A
(x ∷ xs) !!'' fzero = x
(x ∷ xs) !!'' fsuc k = xs !!'' k

-- WARNING: fsuc-ot is sucnak hívják
-- fzero-t meg zeronak

-- Chapter 3 - A Σ
-- Polimorfizmus = Minden típus esetén Stb stb = ∀ típus esetén stb stb
-- polimorfizmus meg úgy unblokk a paraméterek az univerzális kvantifikálást fogják reprezentálni
-- id : {A : Set} → A → A
-- Minden A típus esetén és minden A típusú kifejezés esetén vissza tudok adni egy A típusú kifejezést
-- ∃ = exisztenciális kvantor
-- létezik X hogy Y

--        V erre mondjuk hogy létezik
record Σ (A : Set) (B : A → Set) : Set where
--                  ^ ezzel mondjuk hogy mi igaz az első paraméterre
  constructor _,Σ_
  field
    fst : A     -- a konkrét elem ami létezik
    snd : B fst -- a predikátum ami igaz rá

-- ∃ x: x < 2 = Σ ℕ λ x → x < 2
-- Bolzano-tétel = f : [a,b] → ℝ, f ∈ C[a,b], f(a) * f(b) < 0 ⇒ ∃y ∈ [a,b]: f(y) = 0
--                                                               ^ a tétel a függvényhez sose asszociálja ezt az y-t csak azt mondja hogy létezik
--                                                               azt nem mondja meg mennyi
-- A típuselmélet ilyet nem enged
-- ∃ mindig meg mondja hogy mire mondjuk hogy létezik

σ1 : Σ ℕ λ k → 0 < k
σ1 = 3782136821 ,Σ tt

-- ∀ A típus, ∀ n ∈ ℕ, ∀ (A → Bool), ∀ Vec A n ∃ k ∈ ℕ: Vec A k
filter : {A : Set}{n : ℕ} → (A → Bool) → Vec A n → (Σ ℕ λ k → Vec A k)
filter p [] = zero ,Σ []
filter p (x ∷ vs) with p x
... | false = filter p vs
... | true with filter p vs
... | n ,Σ vec = suc n ,Σ (x ∷ vec)
