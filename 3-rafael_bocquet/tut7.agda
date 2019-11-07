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
BoolRefl = indBool (λ b → BoolEq b b) tt tt

-- Equality for natural numbers:

ℕEq : ℕ → ℕ → Set
ℕEq = λ n m → indℕ (λ _ → ℕ → Set) (indℕ (λ _ → Set) ⊤ (λ _ _ → ⊥)) (λ _ f → indℕ (λ _ → Set) ⊥ (λ k _ → f k)) n m

plus : ℕ → ℕ → ℕ
plus = λ x x₁ → primrec x (λ _ k → suc k) x₁

plusRightId : (x : ℕ) → ℕEq (plus x zero) x
plusRightId = λ x → indℕ (λ x → ℕEq (plus x zero) x) tt (λ n z → z) x

plusLeftId : (x : ℕ) → ℕEq (plus zero x) x
plusLeftId x = indℕ (λ n → ℕEq (plus zero n) n) tt (λ n z → z) x

zero≠suc : (x : ℕ) → ¬ ℕEq zero (suc x)
zero≠suc = λ _ z → z

suc-inj : (x y : ℕ) → ℕEq (suc x) (suc y) → ℕEq x y
suc-inj = λ _ _ z → z


-- Transport: an equality between x : X and y : X can be used to transport from P x to P y, for any dependent type P : X → Set

BoolTrans : (P : Bool → Set) → (x y : Bool) → BoolEq x y → P x → P y
BoolTrans = λ P x y → indBool (λ x → BoolEq x y → P x → P y)
                              (indBool (λ y → BoolEq true y → P true → P y) (λ _ z → z) (λ k → exfalso k) y)
                              (indBool (λ y → BoolEq false y → P false → P y) (λ k → exfalso k) (λ _ z → z) y)
                              x

ℕTrans : (P : ℕ → Set) → (x y : ℕ) → ℕEq x y → P x → P y
ℕTrans = λ P x y x≡y p →
  indℕ (λ x → ∀ y (x≡y : ℕEq x y) (P : ℕ → Set) (p : P x) → P y)
       (indℕ (λ y → (x≡y : ℕEq 0 y) (P : ℕ → Set) → P 0 → P y)
             (λ _ _ z → z)
             (λ _ _ → exfalso))
       (λ x x' → indℕ (λ y → (x≡y : ℕEq (suc x) y) (P : ℕ → Set) → P (suc x) → P y)
                 exfalso
                 (λ n _ x≡y P → x' n x≡y (λ z → P (suc z)))) x y x≡y P p
