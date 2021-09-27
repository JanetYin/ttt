module 2021aut.t2.gy03.demonstration where

open import lib
open import 2021aut.t2.lib

_+0 : ℕ → ℕ
_+0 = λ x → x

-- 0 +0 = 0
-- 1 +0 = 1

_+1 : (x : ℕ) → ℕ
_+1 = λ x → suc x

_+2 : ℕ → ℕ
_+2 = λ x → suc (suc x)

+1or+2 : 𝟚 → ℕ → ℕ
choose : {A : Set} → A × A → 𝟚 → A

--+1or+2 = λ lower → if lower then (_+1) else (_+2)
+1or+2 =  choose ((_+1) , (_+2)) 
-- later:   λ lower → ...
-- later':  λ lower → choose ...
-- later'': choose ...

-- \times = ×
-- \pi    = π
-- \_1    = ₁
choose = λ pair first → if first then π₁ pair else π₂ pair

x : ℕ
x = choose {ℕ} (1 , 2) tt

x' : 𝟚
x' = choose {𝟚} (tt , tt) tt

_+3 : ℕ → ℕ
_+3 = λ x → suc (suc (suc x))

_+10 : ℕ → ℕ
_+10 = λ x → rec x _+1 10
--           rec x _+1 (suc 2)
--           _+1 (rec x _+1 2)
--           _+1 (rec x _+1 (suc 1))
--           _+1 (_+1 (rec x _+1 (suc zero)))
--           _+1 (_+1 (_+1 (x)))
-- rec x f n = n szerinti rekurzió x-ről f-et akalmazgatva

_+_ : ℕ → ℕ → ℕ
_+_ = λ x → rec x _+1
