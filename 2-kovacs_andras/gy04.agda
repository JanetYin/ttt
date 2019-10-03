
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
--   Haskell-ben : (), értéke ()

--   logikai ekvivalencia: A ↔ B = (A → B) × (B → A)
--   unicode: \<->

-- Agda parancs:
--   C-u-C-u-C-c-C-, típus megjelenítése normalizálva
--   C-u-C-u         lehet tenni több parancs elé, normalizáltan
--                   jelennek meg típusok ennek hatására

-- true  ~ inj₁ tt
-- false ~ inj₂ tt
Bool~2 : Bool ↔ (⊤ ⊎ ⊤)
Bool~2 = (λ b → if b then inj₁ tt else inj₂ tt)
       , (λ x → case x (λ _ → true) (λ _ → false))

-- 2.
⊎commutative : (X ⊎ Y) ↔ (Y ⊎ X)
⊎commutative = (λ x → case x (λ x → inj₂ x)
                             λ y → inj₁ y)
             , λ x → case x (λ y → inj₂ y)
                            (λ x → inj₁ x)
-- Haskell-ben: (csak az egyik irány)
-- f :: Either a b -> Either b a
-- f x = case x of
--   Left x  -> Right x
--   Right y -> Left y

-- 3. (bónusz)
⊎assoc : (X ⊎ Y ⊎ Z) ↔ ((X ⊎ Y) ⊎ Z)
⊎assoc = {!!}

-- 4. függvények ⊎-ból: pontosan akkor adható meg függvény ⊎-ból, ha mindkét
--    komponenséből megadható függvény.
⊎→ : ((X ⊎ Y) → Z) ↔ ((X → Z) × (Y → Z))
⊎→ = (λ f → (λ x → f (inj₁ x)) , (λ y → f (inj₂ y)))
   , (λ p xy → case xy (λ x → proj₁ p x)
                       (λ y → proj₂ p y))

-- MECHANIKUS MEGOLDÁSOK_
  -- 1. Goal : A × B    -- rögtön írok (? , ?)
  -- 2. Goal : A → B    -- rögtön írok (λ a → ?)


------------------------------------------------------------
-- ⊥: üres típus (logikai ellentmondás)
-- unicode: \bot
-- használat:   ⊥-elim : ⊥ → A  (tetszőleges A-ra)

-- logikai negáció: ¬ A = A → ⊥
-- (¬ A) -nak pontosan akkor adható meg érték, ha A üres.

-- 5.
⊎unit : (⊥ ⊎ X) ↔ X     -- inj₁ kizárva
                        -- (csak az inj₂ lehetséges!)
⊎unit = (λ bx → case bx
                   (λ p → exfalso p)
                   (λ x → x))
      , (λ x → inj₂ x)

-- exfalso: azt jelöli hogy soha le nem futó kódrészben
-- vagyunk (olyan programágon, amit nem lehet elérni)

-- 6. Példa negáció használatára: Ha ¬ X és X is ismert, az ellentmondáshoz vezet (⊥)
-- C-u-C-u prefix: normalizált típusokat jelenít meg.
non-contradiction : ¬ X → X → ⊥
non-contradiction f x = f x

-- kicsit másképp ugyanaz
non-contradiction2 : ¬ (¬ X × X)
non-contradiction2 = λ p → proj₁ p (proj₂ p)

-- 6. de Morgan szabály
deMorgan1 : ¬ (X ⊎ Y) ↔ (¬ X × ¬ Y)
deMorgan1 = (λ f → (λ x → f (inj₁ x)) , (λ y → f (inj₂ y)))
          , (λ p xy → case xy (proj₁ p) (proj₂ p))


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
