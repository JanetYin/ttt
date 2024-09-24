module en.hf10 where

open import Lib

-- Theorems are in Lib.Nat.Properties.

-- Evil task, the expression would be too long step by step because of the 100,
-- if we let Agda do the work.
p5 : (a : ℕ) → (10 * a + 5) ^ 2 ≡ a * (suc a) * 100 + 25
p5 a = {!   !}

-- Scary at first, on second look it needs a closer inspection.
p6 : (a b c d e : ℕ) →
  (a + b) ^ 2 * 0 + (a * 0 + 0 + c * 0) ≡ 2 * d * 0 + e * (suc e) * 0 + ((a + 0) * 0)
p6 = {!   !}

-- Lots of magic with parentheses.
p7 : (a b : ℕ) → b + a + b + a + b + a ≡ 3 * (b + 0 + a) * 1
p7 = {!   !}

-- Exponentiation magic
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
-- More difficult case, but giving an example is still easy.
p14 : ¬ ((n k : ℕ) → 2 ^ suc n ≡ 3 ^ suc k)
p14 = {!   !}

-- But if we need to prove it for all n, k...!
-- It requires quite a few ideas.
p15 : (n k : ℕ) → 2 ^ suc n ≢ 3 ^ suc k
p15 = {!   !}
