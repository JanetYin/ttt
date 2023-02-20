open import lib
{-
record Σ (A : Type)(B : A → Type) : Type where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public
-}
-- klasszikus logika
{-
prop = Bool  -- proposition, logikai allitas

_&&_ : Bool → Bool → Bool
_&&_ b = if b then_else false

infixl 4 _∧_
_∧_ _∨_ : prop → prop → prop
A ∧ B = A && B
A ∨ B = if A then true else B

⊥' ⊤' : prop
⊥' = false
⊤' = true
-- _∨_, _⊃_
¬'_ : prop → prop
¬'_ = if_then false else true

-- kizart harmadik elve, lem, :
-- lem : (A : prop) → A ∨ (¬' A)

-- ∀ x . P(x)   P : ℕ → Bool
∀' : (ℕ → Bool) → Bool
∀' P = {!P 0 ∧ P 1 ∧ P 2 ∧ P 3!} -- ∧ ...
_>=_ : ℕ → ℕ → Bool
zero  >= zero  = true
zero  >= suc _ = false
suc _ >= zero  = true
suc m >= suc n = m >= n

A : prop -- ∀ n . n >= 0
A = ∀' λ n → n >= 0

A ⊃ B = B ∨ ¬ A
-}

prop = Type  -- Heyting
_∧_ _∨_ _⊃_ : prop → prop → prop

A ∧ B = A × B
A ∨ B = A ⊎ B -- A ∨ B bizonyitasainak a halmaza = { (0,a) | a∈A} ∪ { (1,b) | b∈B}
A ⊃ B = A → B
-- ⊥ = ⊥
-- ⊤ = ⊤
∀' ∃' : (ℕ → prop) → prop -- ∀n.P(n)
∀' P = (n : ℕ) → P n
∃' P = Σ ℕ P
-- ¬ A = A → ⊥

-- predikatum, unaris relacio
module egyik where
  Even : ℕ → prop
  Even zero    = ⊤
  Even (suc zero) = ⊥
  Even (suc (suc n)) = Even n

Even : ℕ → prop
Odd  : ℕ → prop
Even zero = ⊤
Even (suc n) = Odd n
Odd zero = ⊥
Odd (suc n) = Even n

even4 : Even 4 -- = Even(ssssz) = Odd(sssz) = Even(ssz) = Odd(sz) = Even z = ⊤
even4 = tt

-- Odd (3 + n) = Odd (sssn) = Even (ssn) = Odd (sn) = Even n
theorem1 : (n : ℕ) → Even n → Odd (3 + n)
theorem1 = λ n en → en

-- zeros : (n : ℕ) → Vec ℕ n

theorem2 : (n : ℕ) → Even n → Odd (n + 3)
theorem2 zero    en = tt
theorem2 (suc (suc n)) en = theorem2 n en

-- predikatum termeszetes szamon: ℕ → prop
-- (homogen binaris) relacio: ℕ → ℕ → prop
_>=_ : ℕ → ℕ → prop
zero  >= zero  = ⊤
zero  >= suc _ = ⊥
suc _ >= zero  = ⊤
suc m >= suc n = m >= n

-- Brouwer-Heyting-Kolmogorov interpretacio, Curry-Howard izomorfizmus,
-- propositions as types, allitasok mint tipusok

-- Andrej Bauer: 5 steps in accepting constructive mathematics

-- A     ¬ (¬ A) = (A → ⊥) → ⊥

--    {A : Type} → A → (A → B) → B
nna : {A : prop} → A → ¬ ¬ A
nna a na = na a

lemnna : {A : Type} → ((A → ⊥) → ⊥) ↔ (A ∨ (¬ A))
lemnna = {!!}

--    {A : Type} → ((A → ⊥) → ⊥) → A
