module hf03 where

open import Lib

{-
Állapítsd meg, hogy mely kifejezések normálformák!
Ha valamelyik kifejezés nem normálforma, add meg a normálformáját
az órán látott definíciók alapján!

FIGYELEM! A Lib-ben a * fordított sorrendben van definiálva,
annak is megvan a létjogosultsága. Ez akkor derül ki, ha a második paraméter egy konkrét érték
és az elsőben van suc, de nem feltétlen konkrét, akkor egy kicsit többet tud normalizálni, mint ezek a definíciók.

_+_ : ℕ → ℕ → ℕ
zero + b = b
(suc a) + b = suc (a + b)
infixl 6 _+_

_*_ : ℕ → ℕ → ℕ
zero * b = 0
suc a * b = a * b + b -- Ez Lib-ben b + a * b-ként van definiálva.
infixl 7 _*_

4 + 4
λ x → x + 1
λ x → 2 + x
λ n m → n + m

2 * 3
λ x → x * 0
λ x → 0 * x
λ x → x * 1
λ x → 1 * x
λ n m → n * m
λ n m → suc n * m
λ n m → n * suc m

λ x → x + 0 * x
λ n → n * 0 * n + suc n * 2
λ x y → 2 * x + (2 + y) * (3 + y)
-}

{-
Definiáld a triple függvényt, amely egy természetes számot megszoroz hárommal.
Értelemszerűen ne használd a _+_ és _*_ függvényeket!
-}

triple : ℕ → ℕ
triple = {!   !}

-- Definiáld a minMax függvényt, amely két természetes számot rendezett párban növekvő sorba rendez.
minMax : ℕ → ℕ → ℕ × ℕ
minMax = {!   !}

minMax-test1 : minMax 5 5 ≡ (5 , 5)
minMax-test1 = refl
minMax-test2 : minMax 9 4 ≡ (4 , 9)
minMax-test2 = refl
minMax-test3 : minMax 1 10 ≡ (1 , 10)
minMax-test3 = refl
minMax-test4 : (λ x → minMax 0 x) ≡ (λ x → 0 , x)
minMax-test4 = refl

-- Definiáld az even? függvényt, amely egy természetes számról
-- megállapítja, hogy páros-e.
even? : ℕ → Bool
even? = {!!}

even?-test1 : even? 3 ≡ false
even?-test1 = refl
even?-test2 : even? 200 ≡ true
even?-test2 = refl

-- Definiáld az Even függvényt, amely egy természetes számról
-- megállapítja, hogy páros-e, de az eredmény "igazságértékét" típusként jelezzük.
-- A ⊤ mindig triviálisan megadható (hiszen pontosan egy elemű)
-- A ⊥ mindig cáfol (hiszen pontosan nulla elemű).
Even : ℕ → Set
Even = {!!}

Even-test1 : ¬ Even 9
Even-test1 ()
Even-test2 : Even 10
Even-test2 = tt
Even-test3 : ¬ Even 901
Even-test3 ()
Even-test4 : Even 100
Even-test4 = tt

-- Mire is jó ez, ha így van megadva?
-- Például az alábbi feladatot lehet pontosítani, hogy milyen bemenetei lehetnek:
half : (n : ℕ) → Even n → ℕ
-- Meg lehet adni feltételeket az értékeknek (ún. refinement type-okat lehet használni).
-- ℕ a típusa, de mégsem lehet akármi.
-- NEHÉZ FELADAT: A feladat definiálni a half függvényt úgy, hogy "értelmes" legyen,
-- csak páros természetes számnak lesz a fele természetes szám.
half n e = {!!}
-----------------------------------------------------------
-- Definiáld a mod függvényt, amely maradékos osztást végez el és a maradékot adja vissza eredményül.
-- A második paraméter soha nem lehet 0, így a totalitás és egyszerűség kedvéért
-- a második paramétert úgy kell értelmezni, hogy mindig 1-et hozzá kell adni.
-- Tehát pl. mod 100 14 = 100 % (1 + 14) = 100 % 15 = 10
mod : ℕ → ℕ → ℕ
mod a b = {!   !}

mod-test1 : mod 5 1 ≡ 1
mod-test1 = refl
mod-test2 : mod 11 2 ≡ 2
mod-test2 = refl

-- Az előző alapján már egyszerűbb feladat:
-- Definiáld a div függvényt, amely egész osztást végez el.
-- A második paraméterre ugyanaz érvényes, mint az előző feladatban.
div : ℕ → ℕ → ℕ
div a b = {!!}
div-test1 : div 5 1 ≡ 2
div-test1 = refl
div-test2 : div 11 2 ≡ 3
div-test2 = refl
--------------------------------

iteNat : {A : Set} → A → (A → A) → ℕ → A
iteNat z s zero = z
iteNat z s (suc n) = s (iteNat z s n)

recNat : {A : Set} → A → (ℕ → A → A) → ℕ → A
recNat z s zero = z
recNat z s (suc n) = s n (recNat z s n)

-- Add meg iteNat-ot mintaillesztés nélkül, recNat segítségével
iteNat' : {A : Set} → A → (A → A) → ℕ → A
iteNat' = {!!}

iteNat'-test1 : {A : Set}{z : A}{s : A → A} → iteNat' z s zero ≡ z
iteNat'-test1 = refl
iteNat'-test2 : {A : Set}{z : A}{s : A → A}{n : ℕ} → iteNat' z s (suc n) ≡ s (iteNat' z s n)
iteNat'-test2 = refl

-- NEHÉZ FELADAT!
-- Add meg recNat-ot mintaillesztés nélkül, iteNat segítségével
recNat' : {A : Set} → A → (ℕ → A → A) → ℕ → A
recNat' = {!!}

recNat'-test1 : {A : Set}{z : A}{s : ℕ → A → A} → recNat' z s zero ≡ z
recNat'-test1 = refl
recNat'-test2 : {A : Set}{z : A}{s : ℕ → A → A} → recNat' z s 3 ≡ s 2 (s 1 (s 0 z))
recNat'-test2 = refl