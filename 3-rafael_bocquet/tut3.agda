module tut3 where
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

and : Bool × Bool → Bool
and = λ p → if proj₁ p then proj₂ p else false

_+_ : ℕ → ℕ → ℕ
_+_ = λ n m → primrec m (λ n x → suc x) n

pred : ℕ → ℕ
pred = λ n → primrec zero (λ n' _ → n') n

_*_ : ℕ → ℕ
_*_ = {!!}

-- sumTo n = 1 + 2 + ... + n
-- sumTo 0 = 0, sumTo 1 = 1, sumTo 2 = 3, sumTo 3 = 6, ...
sumTo : ℕ → ℕ
sumTo = {!!}

_<_ _≤_ : ℕ → ℕ → Bool
_<_ = {!!}
_≤_ = {!!}

eq : ℕ → ℕ → Bool
eq = {!!}

-- Fibonacci sequence:
--  fib 0 = 1
--  fib 1 = 1
--  fib (suc (suc n)) = fib (suc n) + fib n
fib : ℕ → ℕ
fib = {!!}

--------------------------------------------------------------------------------
-- Coproducts
--------------------------------------------------------------------------------

a1 : Bool ⊎ Bool
a1 = inj₁ {!!}

a2 : Bool ⊎ Bool
a2 = inj₂ {!!}

f1 : Bool ⊎ Bool → Bool
f1 = λ b → case b {!!} {!!}

assoc⊎ : (X ⊎ Y) ⊎ Z ↔ X ⊎ (Y ⊎ Z)
assoc⊎ = {!!}
