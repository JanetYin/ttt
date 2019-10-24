module tut7 where
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

-- Equality for booleans
-- We can define the equality predicate for booleans by induction:

BoolEq : Bool → Bool → Set
BoolEq = λ a b → if a then if b then ⊤ else ⊥ else if b then ⊥ else ⊤

-- It is defined in the same way as the equality test, but returning types instead of booleans.
-- We can use it to prove equalities:

BoolRefl : (b : Bool) → BoolEq b b
BoolRefl = {!!}

-- Equality for natural numbers:

ℕEq : ℕ → ℕ → Set
ℕEq = {!!}

plus : ℕ → ℕ → ℕ
plus = {!!}

plusRightId : (x : ℕ) → ℕEq (plus x zero) x
plusRightId = {!!}

zero≠suc : (x : ℕ) → ¬ ℕEq zero (suc x)
zero≠suc = {!!}

suc-inj : (x y : ℕ) → ℕEq (suc x) (suc y) → ℕEq x y
suc-inj = {!!}


-- Transport: an equality between x : X and y : X can be used to transport from P x to P y, for any dependent type P : X → Set

BoolTrans : (P : Bool → Set) → (x y : Bool) → BoolEq x y → P x → P y
BoolTrans = {!!}

ℕTrans : (P : ℕ → Set) → (x y : ℕ) → ℕEq x y → P x → P y
ℕTrans = {!!}
