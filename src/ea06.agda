module ea06 where

open import lib
open import ea05

-- ez az ora 10 perccel rovidebb

-- Π types, szabalyok, special case simply typed

-- Σ types, szabalyok, FlexVec

-- derive ⊎ from Σ and Bool

{-
    Π     Σ
   / \   / \
  /   \ /   \
 →     ×     ⊎
-}

-- simple arithmetic: (Fin m ⊎ Fin n) ↔ Fin (m + n)
--                    (Fin m × Fin n) ↔ Fin (m * n)
--                    (Fin m → Fin n) ↔ Fin (n ^ m)

bool-eq : {m n : ℕ} → Bool ↔ Fin 2
bool-eq = {!!}

-- Fin 2 ⊎ Fin 3 → Fin (2 + 3)
-- example

inj₁f : {m n : ℕ} → Fin m → Fin (m + n) -- induction on i
inj₁f zero = zero
inj₁f (suc i) = suc (inj₁f i)

inj₂f : {m n : ℕ} → Fin n → Fin (m + n) -- induction on m
inj₂f {zero} i = i
inj₂f {suc m} i = suc (inj₂f {m} i)

casef : {m n : ℕ}{C : Set} → Fin (m + n) → (Fin m → C) → (Fin n → C) → C
casef {zero} x f g = g x
casef {suc m} zero f g = f zero
casef {suc m} (suc i) f g = casef {m} i (λ j → f (suc j)) g

sum-eq : {m n : ℕ} → (Fin m ⊎ Fin n) ↔ Fin (m + n)
fst sum-eq = {!!}
snd sum-eq = {!!}

prod-eq : {m n : ℕ} → (Fin m × Fin n) ↔ Fin (m * n)
prod-eq = {!!}

_^_ : ℕ → ℕ → ℕ
a ^ zero    = 1
a ^ (suc n) = a * a ^ n

exp-eq : {m n : ℕ} → (Fin m → Fin n) ↔ Fin (n ^ m)
exp-eq = {!!}

--                                           i<n
-- Σℕ n a = a 0 + a 1 + a 2 + ... + a (n-1) = Σ a(i)
--                                           i=0
Σℕ : (n : ℕ) → (Fin n → ℕ) → ℕ
Σℕ zero    a = 0
Σℕ (suc n) a = a zero + Σℕ n (λ i → a (suc i))

--                                           i<n
-- Πℕ n a = a 0 * a 1 * a 2 * ... * a (n-1) = Π a(i)
--                                           i=0
Πℕ : (n : ℕ) → (Fin n → ℕ) → ℕ
Πℕ zero    a = 1
Πℕ (suc n) a = a zero * Σℕ n (λ i → a (suc i))

sigma-eq : (n : ℕ)(a : Fin n → ℕ) → (Σ (Fin n) λ i → Fin (a i)) ↔ Fin (Σℕ n a)
sigma-eq = {!!}

-- pelda: i = 3, a 0 = 3, a 1 = 2, a 2 = 2, describe the elements

pi-eq : (n : ℕ)(a : Fin n → ℕ) →  ((i : Fin n)   → Fin (a i)) ↔ Fin (Πℕ n a)
pi-eq = {!!}
