module tut2 where
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

f1 : Bool → Bool → Bool × Bool
-- f1 = ? , then C-c C-l
-- f1 = {!!} , C-c C-r in { . }0
-- C-c C-, --> Goal: Bool × Bool
f1 = λ x x₁ → x , x₁

and : Bool × Bool → Bool
and = λ p → if proj₁ p then proj₂ p else false

f2 : (X × Y → Z) → X → Y → Z
f2 = λ f x y → f (x , y)

-- ℕ = \bN
-- zero : ℕ
-- suc : ℕ → ℕ

three : ℕ
three = 3 -- suc (suc (suc zero))

-- primrun
times2 : ℕ → ℕ
times2 = λ x → primrec 0 (λ x' y → suc (suc y)) x

even : ℕ → Bool
even = λ n → primrec true (λ _ y → if y then false else true) n

-- zero + m = m
-- suc n + m = suc (n + m)
_+_ : ℕ → ℕ → ℕ
_+_ = λ n m → primrec m (λ n x → suc x) n

-- Define the pred function using primrec :
--   pred zero = zero
--   pred (suc n) = n
pred : ℕ → ℕ
pred = λ n → primrec zero (λ n' _ → n') n

_<_ _≤_ : ℕ → ℕ → Bool
_<_ = {!!}
_≤_ = {!!}

-- Bonus : define pred with pred = λ n → primrec ? (λ _ y → ?) ?
