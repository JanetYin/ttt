
{-
Elérhetőség: kovacsandras@inf.elte.hu

- Következő óra elejéig:
  BEAD regisztráció: bead.inf.elte.hu, megfelelő Típuselmélet csoport
  felvétele.

- Következő óra elején: kis BEAD feladat, ~5 perc.
-}


-- Lyukak (holes)
------------------------------------------------------------

-- ha ?-et írunk bármilyen kifejezés helyére, akkor
-- C-c-C-l (típusellenőrzés) után a ? lyukká alakul.

open import lib

f1 : Bool → Bool → Bool
f1 = λ x y → {!!}
-- Kurzorral álljunk a lyukba.
-- Parancsok, amelyek egy lyukban használhatók:
--   C-c-C-,      lyuk típus megjelenítése
--   C-c-C-.      lyukba írt kifejezés típusa
--   C-c-C-SPACE  elfogadja lyukba írt kifejezést (ha jól típusozott)
--   C-c-C-r      lyuk finomítása: ha egy kifejezésben a lyukban további ?-ek
--                vannak, akkor azokból új lyukak lesznek.
--   C-c-C-f      kurzor következő lyukba ugrik
--   C-c-C-b      kurzor előző lyukba ugrik
--   C-c-C-a      lyuk kitöltése automatikus kereséssel

-- szorzat unicode: \x
f2 : Bool → Bool × Bool
f2 = λ x → ({!!} , {!!})

-- példa C-c-C-a használatára:
-- X, Y, Z absztrakt típusok
modus-ponens : (X → Y) → X → Y
modus-ponens = λ f x → f x

-- kicsit bonyolultabb
S-axiom : (X → Y → Z) → (X → Y) → X → Z
S-axiom = λ z z₁ z₂ → z z₂ (z₁ z₂)  -- C-c-C-a lyukból megadja ezt

-- lib.agda frissítése: repo könyvtárában parancssor:
--     git pull
-- minden gyakorlat előtt frissítsünk



-- ℕ-függvények, primitív rekurzió
------------------------------------------------------------

-- természetes szám: \bN
-- aláindexelés: \_x
--   így néz ki: Aₓ
-- felülindex: \^x
--   így néz ki: Aˣ
-- nyíl: \r \l \u \d   (right, left, up, down)


-- szeretnénk ℕ → .. függvényt írni
-- primitív rekurzióval

-- duplázzunk meg egy természetes számot
-- lib-ben található: primrec nevű függvény
-- típusa: {A : Set} → A → (ℕ → A → A) → ℕ → A
double : ℕ → ℕ
double = λ n →
  primrec
    -- zero-t mire képezzük le
    zero
    -- (suc n)-t mire képezzük le
    (λ n rec → suc (suc rec))
       -- n   : n-re hivatkozik
       -- rec : rekurzív hívás eredménye
       --         n-ből

       -- suc (suc rec):
       --   rec = n*2
       --   suc (suc rec) = 2 + n*2
       --                 = (n + 1)*2
    n

-- tesztek : C-c-C-n double 10
-- normalizázás: C-c-C-n

not : Bool → Bool
not = λ b → if b then false else true

-- feladat
isEven : ℕ → Bool
isEven = λ n → primrec
  -- isEven 0 = true
  true
  -- isEven (suc n) = not (isEven n)
  (λ n isEven-n → not (isEven-n))
  n

-- Majdnem akármilyen nevet adhatunk változónak, de (,),{,},λ nem szerepelhet
-- benne pl.
f3 : ℕ → ℕ
f3 = λ foobar₀₁ΩΩ-334343ˣˣ → zero
