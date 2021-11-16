module 2021aut.lec.lec10 where

open import lib

Eqℕ : ℕ → ℕ → Set
Eqℕ zero zero = ⊤
Eqℕ zero (suc _) = ⊥
Eqℕ (suc _) zero = ⊥
Eqℕ (suc a) (suc b) = Eqℕ a b

reflℕ : (a : ℕ) → Eqℕ a a
reflℕ = indℕ (λ a → Eqℕ a a) triv (λ n e → e)

_+_ : ℕ → ℕ → ℕ
-- _+_ = λ a b → rec b suc a
zero + b = b
suc n + b = suc (n + b)

2+3=5 : Eqℕ (2 + 3) 5
2+3=5 = triv
-- 2 + 3 = suc (suc zero) + 3 = suc (suc zero + 3) = suc (suc (zero + 3)) = suc (suc 3) = 5

0+a=a : ∀ a → Eqℕ (0 + a) a
0+a=a = reflℕ

a+0=a : ∀ a → Eqℕ (a + 0) a
a+0=a = indℕ (λ a → Eqℕ (a + 0) a) triv (λ n e → e)

+ass : (a b c : ℕ) → Eqℕ ((a + b) + c) (a + (b + c))
+ass = λ a b c → indℕ (λ n → Eqℕ ((n + b) + c) (n + (b + c)))
  (reflℕ (b + c))
  (λ n ih → ih)
  a

-- +-al ℕ monoidot alkotnak

transportℕ : (P : ℕ → Set)(a b : ℕ) → Eqℕ a b → P a → P b
transportℕ P zero    zero    e u = u
transportℕ P (suc a) (suc b) e u = transportℕ (λ x → P (suc x)) a b e u

sym : (a b : ℕ) → Eqℕ a b → Eqℕ b a
sym a b e = transportℕ (λ x → Eqℕ x a) a b e (reflℕ a) 

trans : (a b c : ℕ) → Eqℕ a b → Eqℕ b c → Eqℕ a c
trans a b c e f = transportℕ (λ a → Eqℕ a c) b a (sym a b e) f

-- kommutativ a monoid!
-- a + 0 = 0 + a =(def.szerint) a
-- a + suc b = suc a + b =(def.szerint) suc (a + b)

+suc : (a b : ℕ) → Eqℕ (a + suc b) (suc a + b)
+suc a b = indℕ (λ a → Eqℕ (a + suc b) (suc a + b))
  (reflℕ b)
  (λ n e → e)
  a

+comm' : (a b : ℕ) → Eqℕ (a + b) (b + a)
+comm' = λ a b → indℕ (λ a → Eqℕ (a + b) (b + a))
  (sym (b + 0) b (a+0=a b))
  (λ n e → transportℕ (Eqℕ (suc (n + b))) (suc b + n) (b + suc n) (sym (b + suc n) (suc (b + n)) (+suc b n)) e)
  a

+comm : (a b : ℕ) → Eqℕ (a + b) (b + a)
+comm = λ a b → indℕ (λ a → Eqℕ (a + b) (b + a))
  (sym (b + 0) b (a+0=a b))
  (λ n e → trans (suc n + b) (suc b + n) (b + suc n)
    e
    (sym (b + suc n) (suc b + n) (+suc b n)))
  a
-- (+suc b n) : Eqℕ (b + suc n) (suc b + n)
-- e          : Eqℕ (suc n + b) (suc b + n)
-- kell       : Eqℕ (suc n + b) (b + suc n)
-- 
--                e                sym ? ? (+suc b n)
--  (suc n + b) =====> (suc b + n) ===================> (b + suc n)

noinv : ¬ ((a : ℕ) → Σ ℕ λ a⁻¹ → Eqℕ (a + a⁻¹) 0)
noinv = λ f → π₂ (f 1)  -- Σ ℕ (λ a → ⊥) = ℕ × ⊥    A × B = Σ A λ _ → B
-- Eqℕ (1 + a) 0 = Eqℕ (suc a) zero

_≤_ : ℕ → ℕ → Set
a ≤ b = Σ ℕ λ c → Eqℕ (c + a) b

10≤13 : 10 ≤ 13
10≤13 = 3 , triv

-- HF gondolkozni!
¬10≤8 : ¬ (10 ≤ 8)
¬10≤8 = λ f → indℕ (λ n → Eqℕ (n + 10) 8 → ⊥)
  (λ b → b)
  (λ n w e → w {!!})
  (π₁ f) (π₂ f)
