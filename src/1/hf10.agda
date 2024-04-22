module hf10 where

open import Lib

-- Lib.Nat.Properties-ben vannak a tételek.

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
p8 : (x y z : ℕ) → (27 ^ x) ^ y * 9 ^ z ≡ 3 ^ (3 * x * y + 2 * z)
p8 = {!   !}

------------------------------------------------------------------

task1 : ¬ ((n : ℕ) → n ≡ 3)
task1 = {!   !}

task2 : {n : ℕ} → n ≡ 3 → n ≢ 10
task2 = {!   !}

task3 : ∀ n → Σ ℕ (n ≢_)
task3 = {!   !}

task4 : Σ ℕ (λ n → ∀ m → n ≢ suc m)
task4 = {!   !}

p13 : ¬ Σ ℕ (λ n → ∀ x → x + suc n ≡ x)
p13 = {!   !}

----------------------------
-- Nehezebb eset, de példát mondani továbbra is egyszerű.
p14 : ¬ ((n k : ℕ) → 2 ^ suc n ≡ 3 ^ suc k)
p14 = {!   !}

-- Na de ha minden n,k-ra kell bizonyítani...!
-- Egy jó pár ötlet is kell hozzá.
p15 : (n k : ℕ) → 2 ^ suc n ≢ 3 ^ suc k
p15 = {!   !}
