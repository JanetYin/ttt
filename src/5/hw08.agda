open import Lib hiding (ℕ∞→ℕ)
open import Lib.Containers.Vector
open import Lib.Containers.Stream
open import Agda.Builtin.Bool

-- Írd meg a a szorzást ℕ∞-okkal.
-- Ez nehéz; zh-ban ilyen nehéz nem lesz. Sok beágyazott with kell hozzá.
-- A ℕ-os megfelelő segít.
-- A szintaxishoz segítség: https://agda.readthedocs.io/en/v2.6.4/language/with-abstraction.html
_*∞_ : ℕ∞ -> ℕ∞ -> ℕ∞
_*∞_ = {!!}

-- Add meg a rákövetkező ℕ∞-ot.
suc∞ : ℕ∞ -> ℕ∞
suc∞ = {!!}

-- Miért nem lehet definiálni ezt a függvényt (vagyis eldönteni, hogy véges-e egy ℕ∞ vagy sem)?
isFinite : ℕ∞ -> Bool
isFinite = {!!}

-- Írj Streamet, amiben egymás utáni növekvő sorrendben vannak a ℕ∞-ok.
coNatStream : Stream ℕ∞
coNatStream = {!!}

-- Mi a baj ezzel a tesztesettel? Javítsd ki.
coNatTest : 1 ≡ 1
coNatTest = refl

-- Próbáld meg "vakon" újraimplementálni az órai ℕ∞→ℕ függvényt.
-- Ha segítség kell, leshetsz onnan.
ℕ∞→ℕ : ℕ → ℕ∞ → Maybe ℕ
ℕ∞→ℕ = {!!}

---------------------------------------------------

-- Cseréld le egy nemüres vektor első elemét a megadottra.
swapHead : ∀{i}{A : Set i}{n : ℕ} -> A -> Vec A (suc n) -> Vec A (suc n)
swapHead = {!!}

-- Helyezd át a bal oldali vektor első elemét a jobb oldali vektorra.
-- Miért az a típusszignatúra, ami?
moveHead : ∀{i}{A : Set i}{n m : ℕ}
               -> Vec A (suc n) × Vec A m -> Vec A n × Vec A (suc m)
moveHead = {!!}

-- Ha sok időd van, próbálj meg szokásos listás haskelles függvényeket megírni vektorokra.
-- Mi az, amit sikerül; mi az, amit nem? Mi lehet az összefüggés?
