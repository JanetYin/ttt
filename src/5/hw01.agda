open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Equality

--------------------------------------------------
-- 1. először fejben/papíron átgondolandó kérdések

-- melyik billentyűkombinációval kell az Emacsben egy fájlt:
  -- megnyitni,
  -- menteni,
  -- más néven menteni?
-- hogyan illesztünk be Emacsben a vágólapról?

-- melyik billentyűkombinációval kell egy Agda-fájlt betölteni (ezt fogjuk sokszor nyomogatni)?
-- hogyan kell egy lyukat létrehozni?
-- melyik billentyűkombinációval kell egy lyukra:
  -- megnézni, hogy milyen típusú kifejezést vár a rendszer;
  -- összehasonlítani ezt az éppen beírt dolog típusával;
  -- elfogadtatni a beírt kifejezést ("betölteni" a lyukat)?
-- hogyan kell kiértékelni egy tetszőleges kifejezést?
-- hogyan kell megnézni egy tetszőleges kifejezés típusát?

-- mit kell beírni az Agda-módos Emacsbe ahhoz, hogy az alábbi karaktersorozatokat kapd?
-- (írd le backslashekkel; pl. "\Gl x \r x + 2" a "λ x → x + 2"-höz)
-- Βασιλεια (Basileia)
-- 𝕄𝕖𝕥𝕣𝕠𝟚
-- abs : ℤ → ℕ
-- λ ε 0<ε → ball (ε , 0<ε) x y


--------------------------------------------------
-- 2. most pedig pár gyakorlati feladat

-- ez a következő feladathoz kell
add3 : ℕ → ℕ
add3 x = x + 3

-- állítsd elő a 7-et az add3 függvény kétszeri alkalmazásával; fogadtasd el az eredményt az Agdával is
seven : ℕ
seven = {!!}
-- ez egy teszt; piros lesz, ha nem 7
-- még nem kell érteni, hogy működik
sevenTest : seven ≡ 7
sevenTest = refl

-- C-c C-n-nel értékeld ki, hogy ℕ → (ℕ → ℕ)
-- mire következtetsz ebből?

-- kommenteld ki az alábbi két sort és hozz létre egy-egy lyukat a + előtt és a + után:
--nat : ℕ
--nat = {-ide egy lyuk-} + {-ide egy lyuk-}

-- töltsd ki a lyukakat természetes számokkal; ellenőrizd, hogy a beírt dolgok típushelyesek-e és fogadtasd el őket az Agdával

-- írj függvényt a következő típuokkal:
tr1 : ℕ → (ℕ → ℕ) → ℕ
tr1 = {!!}
tr2 : ℕ → ℕ → (ℕ → ℕ)
tr2 = {!!}

-- mi ennek a típusa? és a jelentése?
weird = (λ n m -> n + 2 * m) ((λ x -> 1 + x) (add3 5))
