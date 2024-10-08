module hf11 where

open import Lib

-- Lib.Nat.Properties-ben vannak a tételek.

-- Gonosz feladat, a 100 miatt túl hosszú lenne a kifejezés lépésenként,
-- ha hagynánk agdát is dolgozni.
p5 : (a : ℕ) → (10 * a + 5) ^' 2 ≡ a * (suc a) * 100 + 25
p5 = {!   !}

-- Elsőre ijesztő, másodjára jobban meg kell nézni, hogy mi is van.
p6 : (a b c d e : ℕ) →
  (a + b) ^' 2 * 0 + (a * 0 + 0 + c * 0) ≡ 2 * d * 0 + e * (suc e) * 0 + ((a + 0) * 0)
p6 = {!   !}

-- Sok varázslás zárójellel.
p7 : (a b : ℕ) → b + a + b + a + b + a ≡ 3 * (b + 0 + a) * 1
p7 = {!   !}

-- Hatványozás mágia
p8 : (x y z : ℕ) → (27 ^' x) ^' y * 9 ^' z ≡ 3 ^' (3 * x * y + 2 * z)
p8 = {!   !}
------------------------------------------------------------------
-- ÚJ DOLOG INNENTŐL LEFELÉ: (nyilván nem ilyen lesz a +/-)
-- A nyolc utolsó feladathoz új dolog kell, ≢-t még nem bizonyítottunk.
-- Nem nagy varázslat, egyértelmű értékek esetén agda magától ki tudja találni,
-- hogy nem fog menni, pl (0 ≡ 1)-ről tudja agda, hogy kamu.

p9' : 0 ≢ the ℕ 1
p9' = {!   !}

p9 : 2 * 2 ≢ 5 * 1
p9 = {!   !}

-- Egyszerűbb, amikor mondani kell egy ellenpéldát:
p10 : ¬ ((n : ℕ) → n + 2 ≡ n + 1)
p10 = {!   !}

-- ...mintsem bizonyítani, hogy ez a kettő sosem lesz egyenlő:
p11 : (n : ℕ) → n + 2 ≢ n + 1
p11 = {!   !}

-----------------------------------------------
-- Nem léteziket más dolog bizonyítani.
p12 : ¬ Σ ℕ (λ n → n + n ≡ 3)
p12 = {!   !}

p13 : ¬ Σ ℕ (λ n → ∀ x → x + suc n ≡ x)
p13 = {!   !}

----------------------------
-- Nehezebb eset, de példát mondani továbbra is egyszerű.
p14 : ¬ ((n k : ℕ) → 2 ^' suc n ≡ 3 ^' suc k)
p14 = {!   !}

-- Na de ha minden n,k-ra kell bizonyítani...!
-- Lehet bizonyítani, de nem feltétlen ajánlom, hogy most foglalkozzatok
-- ezzel, iszonyatosan hosszú a bizonyítása és egy jó pár ötlet is kell hozzá.
p15 : (n k : ℕ) → 2 ^' suc n ≢ 3 ^' suc k
p15 = {!   !}