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

_*_ : ℕ → ℕ → ℕ
_*_ = λ n m → primrec zero (λ _ x → x + n) m

-- sumTo n = 1 + 2 + ... + n
-- sumTo 0 = 0, sumTo 1 = 1, sumTo 2 = 3, sumTo 3 = 6, ...
sumTo : ℕ → ℕ
sumTo = λ n → primrec zero (λ x y → suc x + y) n

isZero : ℕ → Bool
isZero = λ n → primrec true (λ _ _ → false) n

-- Using pattern matching, we would define _≤_ like this:
-- n ≤ 0     = isZero n
-- n ≤ suc m = pred n ≤ m
-- However, if we try to define
--   _≤_ = λ n m → primrec (isZero n) (λ _ y → ?) m
-- we are stuck, because we have y = "n ≤ m",
--   but we can't compute "n ≤ suc m" from y
--
-- Instead, we define a function that corresponds to the following pattern matching definition:
-- _≤ 0     = λ n → isZero n
-- _≤ suc m = λ n → pred n ≤ m
_<_ _≤_ : ℕ → ℕ → Bool
_≤_ = λ n m → primrec (λ n → isZero n) (λ _ f n → f (pred n)) m n
_<_ = λ n m → primrec (λ n → false) (λ _ f n → primrec true (λ n' _ → f n') n) m n

-- eq 0       m       = isZero m
-- eq (suc n) zero    = false
-- eq (suc n) (suc m) = eq n m
eq : ℕ → ℕ → Bool
eq = λ n m → and (n ≤ m , m ≤ n)

-- Fibonacci sequence:
--  fib 0 = 1
--  fib 1 = 1
--  fib (suc (suc n)) = fib (suc n) + fib n
--  fib 2 = 2, fib 3 = 3, fib 4 = 5, fib 5 = 8, fib 6 = 13, ...
fib : ℕ → ℕ
fib = λ n → proj₁ (primrec (1 , 1)
                           (λ m fm → (proj₂ fm)
                                   , (proj₁ fm + proj₂ fm)) n)

--------------------------------------------------------------------------------
-- Coproducts
--------------------------------------------------------------------------------

-- Rules for coproducts:
-- inj₁ : A → A ⊎ B
-- inj₂ : B → A ⊎ B
-- case : A ⊎ B → (A → C) → (B → C) → C

-- a1 : Bool ⊎ Bool
-- a1 = inj₁ {!!}

-- a2 : Bool ⊎ Bool
-- a2 = inj₂ {!!}

-- f1 : Bool ⊎ Bool → Bool
-- f1 = λ b → case b {!!} {!!}

-- assoc⊎ : (X ⊎ Y) ⊎ Z ↔ X ⊎ (Y ⊎ Z)
-- assoc⊎ = {!!}
