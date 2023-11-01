module hw055 where

open import Lib

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A
infixr 5 _∷_

-- Definiáld a minMax' függvényt, amely két természetes számot rendezett párban növekvő sorba rendez.
-- Libben már van egy minMax; azért aposztrófos.
minMax' : ℕ → ℕ → ℕ × ℕ
minMax' = {!   !}

minMax-test1 : minMax' 5 5 ≡ (5 , 5)
minMax-test1 = refl
minMax-test2 : minMax' 9 4 ≡ (4 , 9)
minMax-test2 = refl
minMax-test3 : minMax' 1 10 ≡ (1 , 10)
minMax-test3 = refl
minMax-test4 : (λ x → minMax' 0 x) ≡ (λ x → 0 , x)
minMax-test4 = refl

-- Definiáld az Even függvényt, amely egy természetes számról
-- megállapítja, hogy páros-e, de az eredmény "igazságértékét" típusként jelezzük.
-- A ⊤ mindig triviálisan megadható (hiszen pontosan egy elemű)
-- A ⊥ mindig cáfol (hiszen pontosan nulla elemű).
-- Szóval adja vissza a ⊤ típust páros számra, a ⊥ típust páratlan számra.
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

-- Hasonló módon lehet a predet picit szebbé tenni.
-- Definiáld a NonZero függvényt, ami típusként jelzi, hogy egy természetes szám nemnulla-e.
NonZero : ℕ -> Set
NonZero = {!!}

NonZero-test1 : ¬ NonZero 0
NonZero-test1 ()
NonZero-test2 : NonZero 1
NonZero-test2 = tt

-- Ennek segítségével szépíthetjük a predet, hogy csak nemnulla számot kaphasson:
safePred : (n : ℕ) -> NonZero n -> ℕ
safePred = {!!}

-- Listához hasonlóan írj egyet, ami ⊤-ot ad vissza, ha nem üres a lista.
NonEmpty : {A : Set} -> List A -> Set
NonEmpty = ?

-- És így lehet egy biztonságos headet.
safeHead : {A : Set} (xs : List A) -> NonEmpty xs -> A
safeHead = ?
