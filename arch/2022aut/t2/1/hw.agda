open import Agda.Builtin.Nat renaming (Nat to ℕ) 

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

-- mit kell beírni az Agda-módos Emacsbe ahhoz, hogy az alábbi karaktersorozatot kapd:
-- abs : ℤ → ℕ
-- (írd le backslashekkel; pl. "\Gl x \r x + 2" a "λ x → x + 2"-höz) 

--------------------------------------------------
-- 2. most pedig pár gyakorlati feladat
-- ez a következő feladathoz kell
add3 : ℕ → ℕ
add3 x = x + 3

-- állítsd elő a 7-et az add3 függvénnyel; fogadtasd el az eredményt az Agdával is (persze ő most csak a típust tudja ellenőrizni)
seven : ℕ
seven = {!!}

-- C-c C-n-nel értékeld ki, hogy ℕ → (ℕ → ℕ)
-- mire következtetsz ebből?

-- kommenteld ki az alábbi két sort és hozz létre egy-egy lyukat a + előtt és a + után:
--nat : ℕ
--nat = {-ide egy lyuk-} + {-ide egy lyuk-}

-- töltsd ki a lyukakat természetes számokkal; ellenőrizd, hogy a beírt dolgok típushelyesek-e és fogadtasd el őket az Agdával

-- írj függvényt a következő típussal:
tr : ℕ → ℕ → ℕ → ℕ
tr = {!!}
