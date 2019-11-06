module tut6 where
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
-- Universes (Set), dependent functions and vectors
--------------------------------------------------------------------------------

-- The syntax for dependent functions is "(a : A) → B(a)"

-- This is the definition of the induction principle for ℕ
ℕInd : ∀ {i} (P : ℕ → Set i)
            → P zero
            → ((n : ℕ) → P n → P (suc n))
            → (n : ℕ) → P n
ℕInd P pz ps zero    = pz
ℕInd P pz ps (suc n) = ps n (ℕInd P pz ps n)

-- and the definition of the induction principle for Bool
BoolInd : (P : Bool → Set) → P true → P false → (b : Bool) → P b
BoolInd P pt pf true  = pt
BoolInd P pt pf false = pf

-- A ^ n = A × A × A × ... × ⊤    (n times)
infix 3 _^_
_^_ : Set → ℕ → Set
_^_ = λ A n → primrec ⊤ (λ _ B → A × B) n

head : (A : Set) → (n : ℕ) → A ^ (suc n) → A
head = λ A n a → proj₁ a

-- replicate n a = (a , a , ... , a)    (n times)
replicate : (A : Set) → (n : ℕ) → A → A ^ n
replicate = λ A n x → ℕInd (λ n → A ^ n) tt (λ _ xs → x , xs) n

-- snoc a (x , y , ... , z) = (a , x , y , ... , z)
cons : (A : Set) → (n : ℕ) → (a : A) → A ^ n → A ^ (suc n)
cons = λ A n x xs → x , xs

-- snoc (x , y , ... , z) a = (x , y , ... , z , a)
snoc : (A : Set) → (n : ℕ) → A ^ n → (a : A) → A ^ (suc n)
snoc = λ A n xs a → ℕInd (λ n → A ^ n → A ^ suc n) (λ _ → a , tt) (λ _ f xs → proj₁ xs , f (proj₂ xs)) n xs

-- count n = (1 , 2 , ... , n)
count : (n : ℕ) → ℕ ^ n
count = λ n → ℕInd (λ n → ℕ ^ n) tt (λ i xs → snoc ℕ i xs (suc i)) n

-- reverse (x , y, ..., z) = (z , ... , y, x)
reverse : (A : Set) → (n : ℕ) → A ^ n → A ^ n
reverse = λ A n z → ℕInd (λ n → A ^ n → A ^ n) (λ _ → tt) (λ n f xs → snoc A n (f (proj₂ xs)) (proj₁ xs)) n z

--------------------------------------------------------------------------------
-- Equality predicate for booleans
--------------------------------------------------------------------------------

BoolEq : Bool → Bool → Set
BoolEq = {!!}

BoolRefl : (b : Bool) → BoolEq b b
BoolRefl = {!!}

BoolSym : (b c : Bool) → BoolEq b c → BoolEq c b
BoolSym = {!!}

BoolTrans : (a b c : Bool) → BoolEq a b → BoolEq b c → BoolEq a c
BoolTrans = {!!}
