module hf11 where

open import lib
open import proofs

p1 : (a b : ℕ) → (a + b) ^ 2 ≡ a ^ 2 + 2 * a * b + b ^ 2
p1 = {!!}

p2 : (a b c : ℕ) → c * (b + 1 + a) ≡ a * c + b * c + c
p2 = {!!}

p3 : (a b : ℕ) → a + a + b + a * 0 ≡ 2 * a + b
p3 = {!!}

p4 : (x y : ℕ) → ((x + (y + zero)) + x) ≡ (2 * x + y)
p4 = {!!}

-- Gonosz feladat, a 100 miatt túl hosszú lenne a kifejezés lépésenként,
-- ha hagynánk agdát is dolgozni.
p5 : (a : ℕ) → (10 * a + 5) ^ 2 ≡ a * (suc a) * 100 + 25
p5 = {!   !}

-- Elsőre ijesztő, másodjára jobban meg kell nézni, hogy mi is van.
p6 : (a b c d e : ℕ) →
  (a + b) ^ 2 * 0 + (a * 0 + 0 + c * 0) ≡ 2 * d * 0 + e * (suc e) * 0 + ((a + 0) * 0)
p6 = {!   !}

-- Sok varázslás zárójellel.
p7 : (a b : ℕ) → b + a + b + a + b + a ≡ 3 * (b + 0 + a) * 1
p7 = {!   !}

-- Hatványozás mágia
p8 : (x y z : ℕ) → (27 ^ x) ^ y + 9 ^ z ≡ 3 ^ (3 * x * y + 2 * z)
p8 = {!   !}
------------------------------------------------------------------
-- ÚJ DOLOG INNENTŐL LEFELÉ: (nyilván nem ilyen lesz a +/-)
-- A három utolsó feladathoz új dolog kell, ≢-t még nem bizonyítottunk.
-- Nem nagy varázslat, egyértelmű értékek esetén agda magától ki tudja találni,
-- hogy nem fog menni, pl (0 ≡ 1)-ről tudja agda, hogy kamu.

p9 : 2 * 2 ≢ 5 * 1
p9 = {!   !}

-- Egyszerűbb, amikor mondani kell egy ellenpéldát:
p10 : ¬ ((n : ℕ) → n + 2 ≡ n + 1)
p10 = {!   !}

-- ...mintsem bizonyítani, hogy ez a kettő sosem lesz egyenlő:
p11 : (n : ℕ) → n + 2 ≢ n + 1
p11 = {!   !}

----------------------------
-- Nehezebb eset, de példát mondani továbbra is egyszerű.
p12 : ¬ ((n k : ℕ) → 2 ^ suc n ≡ 3 ^ suc k)
p12 = {!   !}

-- Na de ha minden n,k-ra kell bizonyítani...!
-- Lehet bizonyítani, de nem feltétlen ajánlom, hogy most foglalkozzatok
-- ezzel, iszonyatosan hosszú a bizonyítása és egy jó pár ötlet is kell hozzá.
p13 : (n k : ℕ) → 2 ^ suc n ≢ 3 ^ suc k
p13 = {!   !}
