module tut5 where
open import lib

-- Emacs key bindings (C = Ctrl, M = Alt):
-- C-x C-f : create or open a file
-- C-x C-s : save a file
-- C-x C-c : close Emacs
-- M-w : Copy
-- C-y : Paste
--
-- Agda-mode key bindings:
-- C-c C-l : Typecheck
-- C-c C-n : Evaluate
-- C-c C-, : Check the type of a hole
-- C-c C-. : Check the type of a hole, and the type of the expresion in the hole
-- C-c C-SPACE : Fill a hole
-- C-c C-r : Try to automatically fill a hole
--
-- Symbols: λ = \lambda
--          × = \times
--          → = \r
--          ₁ = \_1
--          ₂ = \_2
--          ⊎ = \u+
--          ≤ = \le
--          ↔ = \<->
--          ⊤ = \top
--          ⊥ = \bot
--          ¬ = \neg

--------------------------------------------------------------------------------
-- Negation and the empty type
--------------------------------------------------------------------------------

-- The empty type ⊥ has one elimination rule:
--   exfalso : ⊥ → A        for any type A

-- ¬ X  is the same as  X → ⊥

neg× : ¬ X → ¬ (X × Y)
neg× = {!!}

neg⊎ : ¬ (X ⊎ Y) → ¬ X
neg⊎ = {!!}

f1 : ¬ (X × ¬ X)
f1 = {!!}

return¬ : X → ¬ ¬ X
return¬ = {!!}

f2 : ¬ ¬ ¬ X → ¬ X
f2 = {!!}

dM1 : ¬ (X ⊎ Y) → (¬ X × ¬ Y)
dM1 = {!!}

dM2 : (¬ X × ¬ Y) → ¬ (X ⊎ Y)
dM2 = {!!}

dM3 : (¬ X ⊎ ¬ Y) → ¬ (X × Y)
dM3 = {!!}

DM4 = ¬ (X × Y) → (¬ X ⊎ ¬ Y)
LEM = X ⊎ ¬ X

¬¬LEM : ¬ ¬ LEM
¬¬LEM = {!!}

¬¬DM4 : ¬ ¬ DM4
¬¬DM4 = {!!}

--------------------------------------------------------------------------------
-- Universes (Set), dependent functions and vectors
--------------------------------------------------------------------------------

-- Using the universe Set, we can define for instance:
neg×' : (A B : Set) → ¬ A → ¬ (A × B)
neg×' = λ A B x → λ z → x (proj₁ z)

-- The syntax for dependent functions is "(a : A) → B(a)"

-- This is the definition of the induction principle for ℕ
ℕInd : ∀ {i} (P : ℕ → Set i)
            → P zero
            → ((n : ℕ) → P n → P (suc n))
            → (n : ℕ) → P n
ℕInd P pz ps zero    = pz
ℕInd P pz ps (suc n) = ps n (ℕInd P pz ps n)

-- A ^ n = A × A × A × ... × ⊤    (n times)
infix 3 _^_
_^_ : Set → ℕ → Set
_^_ = {!!}

head : (A : Set) → (n : ℕ) → A ^ (suc n) → A
head = {!!}

-- replicate n a = (a , a , ... , a)    (n times)
replicate : (A : Set) → (n : ℕ) → A → A ^ n
replicate = {!!}

-- count n = (1 , 2 , ... , n)
count : (A : Set) → (n : ℕ) → ℕ ^ n
count = {!!}

-- snoc a (x , y , ... , z) = (a , x , y , ... , z)
cons : (A : Set) → (n : ℕ) → (a : A) → A ^ n → A ^ (suc n)
cons = {!!}

-- snoc (x , y , ... , z) a = (x , y , ... , z , a)
snoc : (A : Set) → (n : ℕ) → A ^ n → (a : A) → A ^ (suc n)
snoc = {!!}
