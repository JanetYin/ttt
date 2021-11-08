{-# OPTIONS --allow-unsolved-metas #-}
module zh05 where

open import lib

-- Add meg típushelyesen az alábbi termeket, exfalso használata nélkül!

-- C-c C-a
task1 : ((⊤ × ⊥) ⊎ ⊤) × (⊤ ⊎ ⊥)
task1 = ι₂ triv , ι₁ triv

-- C-c C-r
task2 : ⊥ → ⊤ × ⊥
task2 = λ x → triv , x

-- :(
task3 : (⊥ × ⊤) ⊎ (⊥ × ⊤)  → ⊤ × ⊥
task3 = λ t → case t (λ z → triv , π₁ z) λ z → triv , π₁ z
