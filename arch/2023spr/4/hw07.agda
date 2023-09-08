open import lib

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

toℕ : {n : ℕ} → Fin n → ℕ
toℕ zero = zero
toℕ (suc k) = suc (toℕ k)

data Vec {i} (A : Set i) : ℕ → Set i where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

_≠0 : ℕ → Set
zero ≠0 = ⊥
(suc _) ≠0 = ⊤

div : (a b : ℕ) .{b≠0 : b ≠0} → ℕ
div a b = div-fuel a b (suc a)
  where
  div-fuel : ℕ → ℕ → ℕ → ℕ
  div-fuel a b zero = 42
  div-fuel a b (suc fuel) = if (b < (suc a)) then (suc (div-fuel (a - b) b fuel)) else zero

-----------------------------------------------------

-- Definiáld a contains függvényt, ami Boolban visszaadja, hogy egy érték benne van-e egy vektorban.
-- A típusszignatúrát is te add meg.
-- Fontos: át kell venned egy olyan (A → A → Bool) típusú függvényt is, ami megvizsgálja, hogy két A típusú érték egyenlő-e. (Ahogy a Haskellben is kéne az Eq típusosztály.)
-- Ez legyen az első nem rejtett paraméter.
contains : {!!}
contains = {!!}

test-contains : contains _==_ 5 (1 ∷ (3 ∷ (5 ∷ []))) ≡ true
test-contains = refl

test-contains2 : contains _==_ 0 (1 ∷ (3 ∷ (5 ∷ []))) ≡ false
test-contains2 = refl

-- Definiáld az előző függvény felhasználásával az intersect függvényt, ami két (akár különböző hosszú!) vektort vár paraméterül,
-- és visszaadja a közös értékeit tartalmazó vektort. Mivel ennek a hosszát nem tudjuk előre, ezt egy szigmába csomagolva add meg.
-- A típusszignatúra kitalálása is a feladat része. Most is az első paraméter legyen az egyenlőségfüggvény.
-- Az egyszerűség kedvéért tegyük fel, hogy mindkét vektorban csupa különböző elem van. Viszont az elemek nem feltétlen rendezettek.

intersect : {!!}
intersect = {!!}

test-intersect : intersect _==_ (5 ∷ (9 ∷ (0 ∷ []))) (0 ∷ (3 ∷ (4 ∷ (5 ∷ [])))) ≡ (2 , (5 ∷ (0 ∷ [])))
test-intersect = refl

-- Írd meg az alábbi izomorfizmust (mit jelent egyébként?).
Σ↔⊎⊎⊎ : ∀{i}{A B C D : Set i} →
   Σ (Fin 4) (λ { zero → A ; (suc zero) → B ; (suc (suc zero)) → C ; (suc (suc (suc zero))) → D })
      ↔  A ⊎ B ⊎ C ⊎ D
fst Σ↔⊎⊎⊎ = {!!}
snd Σ↔⊎⊎⊎ = {!!}

-- Írd meg az alábbi izomorfizmus _első felét_. Ez nehezebb, mert tervezni is kell, hogy ténylegesen bijekció legyen.
-- Segítség: jól jön egy egészosztás; ezt fentre bemásoltam.
-- A második fele nehéz, és kell hozzá olyan is, amit nem tanultunk, de megpróbálhatod, ha sok időd van;)
ΣℕBool↔ℕ :  Σ ℕ Fin ↔ ℕ
fst ΣℕBool↔ℕ = {!!}
snd ΣℕBool↔ℕ n = {!!}
