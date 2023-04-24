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
contains : ∀{i}{A : Set i}{n : ℕ} → (eq : A → A → Bool) → A → Vec A n → Bool
contains eq a [] = false
contains eq a (x ∷ xs) = (eq a x) or (contains eq a xs)
  where
  _or_ : Bool → Bool → Bool
  true or _ = true
  _ or b = b

test-contains : contains _==_ 5 (1 ∷ (3 ∷ (5 ∷ []))) ≡ true
test-contains = refl

test-contains2 : contains _==_ 0 (1 ∷ (3 ∷ (5 ∷ []))) ≡ false
test-contains2 = refl

-- Definiáld az előző függvény felhasználásával az intersect függvényt, ami két (akár különböző hosszú!) vektort vár paraméterül,
-- és visszaadja a közös értékeit tartalmazó vektort. Mivel ennek a hosszát nem tudjuk előre, ezt egy szigmába csomagolva add meg.
-- A típusszignatúra kitalálása is a feladat része. Most is az első paraméter legyen az egyenlőségfüggvény.
-- Az egyszerűség kedvéért tegyük fel, hogy mindkét vektorban csupa különböző elem van. Viszont az elemek nem feltétlen rendezettek.

intersect : ∀{i}{A : Set i}{n m : ℕ} → (eq : A → A → Bool) → Vec A n → Vec A m → Σ ℕ (Vec A)
intersect _ [] _ = 0 , []
intersect _ _ [] = 0 , []
intersect eq (x ∷ xs) ys = if (contains eq x ys) then suc (fst rec) , (x ∷ snd rec) else rec
  where
  rec = intersect eq xs ys

test-intersect : intersect _==_ (5 ∷ (9 ∷ (0 ∷ []))) (0 ∷ (3 ∷ (4 ∷ (5 ∷ [])))) ≡ (2 , (5 ∷ (0 ∷ [])))
test-intersect = refl

-- Írd meg az alábbi izomorfizmust (mit jelent egyébként?).
Σ↔⊎⊎⊎ : ∀{i}{A B C D : Set i} →
   Σ (Fin 4) (λ { zero → A ; (suc zero) → B ; (suc (suc zero)) → C ; (suc (suc (suc zero))) → D })
      ↔  A ⊎ B ⊎ C ⊎ D
fst Σ↔⊎⊎⊎ (zero , a) = inl a
fst Σ↔⊎⊎⊎ (suc zero , b) = inr (inl b)
fst Σ↔⊎⊎⊎ (suc (suc zero) , c) = inr (inr (inl c))
fst Σ↔⊎⊎⊎ (suc (suc (suc zero)) , d) = inr (inr (inr d))
snd Σ↔⊎⊎⊎ (inl a) = zero , a
snd Σ↔⊎⊎⊎ (inr (inl b)) = suc zero , b
snd Σ↔⊎⊎⊎ (inr (inr (inl c))) = suc (suc zero) , c
snd Σ↔⊎⊎⊎ (inr (inr (inr d))) = suc (suc (suc zero)) , d

-- Írd meg az alábbi izomorfizmus _első felét_. Ez nehezebb, mert tervezni is kell, hogy ténylegesen bijekció legyen.
-- Segítség: jól jön egy egészosztás; ezt fentre bemásoltam.
-- A második fele nehéz, és kell hozzá olyan is, amit nem tanultunk, de megpróbálhatod, ha sok időd van;)

{-
(n : ℕ)      Fin n
0         |
1         | zero {0}
2         | zero,    suc zero
3         | zero,    suc zero, suc (suc zero)
4         | zero,    suc zero, suc (suc zero), suc (suc (suc zero))

hány van előtte?
ha n , k a rekord:
n * (n - 1) / 2 + k
-}

ΣℕFin↔ℕ :  Σ ℕ Fin ↔ ℕ
fst ΣℕFin↔ℕ (suc n-1 , k) = let n = (suc n-1) in div (n * n-1) 2 + toℕ k
snd ΣℕFin↔ℕ n = {!!}
