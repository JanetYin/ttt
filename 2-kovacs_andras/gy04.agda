
-- ⊤, ⊥, ⊎, ℕ feladatok
------------------------------------------------------------

open import lib

-- figyelem: "gyakfeladatok*.agda" néven található fájlok ebben
-- a könyvtárban. Megoldásuk javasolt.


-- 1. feladat. Bool izomorf a (⊤ ⊎ ⊤) típussal, mindkettőnek
-- két lehetséges értéke van. Definiáljuk az oda-vissza konverziót.

-- emlékeztető:
--   ⊤ : egy elemű típus, az egyetlen értéke: tt
--   unicode: \top

--   logikai ekvivalencia: A ↔ B = (A → B) × (B → A)
--   unicode: \<->

-- Agda parancs:
--   C-u-C-u-C-c-C-, típus megjelenítése normalizálva
--   C-u-C-u         lehet tenni több parancs elé, normalizáltan
--                   jelennek meg dolgok ettől

Bool~2 : Bool ↔ (⊤ ⊎ ⊤)
Bool~2 = {!!}

-- 2.
⊎commutative : (X ⊎ Y) ↔ (Y ⊎ X)
⊎commutative = (λ xy → case xy inj₂ inj₁) , (λ x → case x inj₂ inj₁)

-- 3. (bónusz)
⊎assoc : (X ⊎ Y ⊎ Z) ↔ ((X ⊎ Y) ⊎ Z)
⊎assoc = {!!}

-- 4. függvények ⊎-ból: pontosan akkor adható meg függvény ⊎-ból, ha mindkét
--    komponenséből megadható függvény.
⊎→ : ((X ⊎ Y) → Z) ↔ ((X → Z) × (Y → Z))
⊎→ = {!!}


------------------------------------------------------------
-- ⊥: üres típus (logikai ellentmondás)
-- unicode: \bot
-- használat:   ⊥-elim : ⊥ → A  (tetszőleges A-ra)

-- logikai negáció: ¬ A = A → ⊥
-- (¬ A) -nak pontosan akkor adható meg érték, ha A üres.

-- 5.
⊎unit : (⊥ ⊎ X) ↔ X
⊎unit = {!!}

-- 6. Példa negáció használatára: Ha ¬ X és X is ismert, az ellentmondáshoz vezet (⊥)
non-contradiction : ¬ X → X → ⊥
non-contradiction = {!!}

-- kicsit másképp ugyanaz
non-contradiction2 : ¬ (¬ X × X)
non-contradiction2 = {!!}

-- 6. de Morgan szabály
deMorgan1 : ¬ (X ⊎ Y) ↔ ¬ X
deMorgan1 = {!!}


-- ℕ feladatok
------------------------------------------------------------

isZero : ℕ → Bool
isZero = {!!}

-- vonjunk ki 1-et egy számból, ha lehet (0 marad 0)
pred : ℕ → ℕ
pred = {!!}

-- zero  + b = b
-- suc a + b = suc (a + b)

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
_+_ = {!!}

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
_*_ = {!!}

-- egyenlőségvizsgálat
eq : ℕ → ℕ → Bool
eq = λ a → primrec
  (λ b       → primrec true  (λ _ _ → false) b)
  (λ _ rec b → primrec false (λ b _ → rec b) b)
  a

-- rekurzív notáció: nem helyes Agda
-- eq : ℕ → ℕ → ℕ
-- eq = λ a -> case a of
--   zero -> λ b → case b of
--     zero  -> true
--     suc _ -> false
--   suc a -> λ b → case b of
--     zero -> false
--     suc b -> eq a b
