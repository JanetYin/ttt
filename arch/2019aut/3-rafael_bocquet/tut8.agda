module tut8 where
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
-- C-c C-c : Case split.
-- C-c C-a : Try to fill a hole automatically
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

-- Pattern matching:
--   Use "C-c C-c {variable name} <Enter>" in a hole to do pattern matching on a variable.
-- Example:
--     n + m = ?
--                      C-c C-c n
--  => zero  + m = ?
--     suc n + m = ?

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc n + m = suc (n + m)

-- Define _*_ using pattern matching instead of primrec
_*_ : ℕ → ℕ → ℕ
zero * m = zero
suc n * m = m + (n * m)

Eqn : ℕ → ℕ → Set
Eqn zero    zero = ⊤
Eqn zero    (suc y) = ⊥
Eqn (suc x) zero = ⊥
Eqn (suc x) (suc y) = Eqn x y

Eqn-refl : (n : ℕ) → Eqn n n
Eqn-refl zero = tt
Eqn-refl (suc n) = Eqn-refl n

plusRightId : (x : ℕ) → Eqn (x + zero) x
plusRightId zero = tt
plusRightId (suc x) = plusRightId x

plusLeftId : (x : ℕ) → Eqn (zero + x) x
plusLeftId x = Eqn-refl x

Eqb : Bool → Bool → Set
Eqb true true = ⊤
Eqb true false = ⊥
Eqb false true = ⊥
Eqb false false = ⊤

-- Transport for Bool
-- Defining it using pattern matching is much simpler than using indBool
Eqb-transp : (P : Bool → Set) (x y : Bool) (p : Eqb x y) → P x → P y
Eqb-transp P true true p a = a
Eqb-transp P true false p a = exfalso p
Eqb-transp P false true p a = exfalso p
Eqb-transp P false false p a = a

not : Bool → Bool
not b = if b then false else true

--------------------------------------------------------------------------------
-- Σ-types
--   Σ : (A : Set) → (B : A → Set) → Set
--   proj₁ : Σ A B → A
--   proj₂ : (p : Σ A B) → B (proj₁ p)
--   _,_ : (a : A) → (b : B a) → Σ A B
--------------------------------------------------------------------------------

prf₀ : (n : ℕ) → Σ ℕ (λ m → ¬ Eqn n m)
prf₀ zero = 1 , exfalso
prf₀ (suc n) = 0 , exfalso

-- not is surjective : for every boolean b, there is some boolean x such that (not x = b)
not-surjective : (b : Bool) → Σ Bool (λ x → Eqb (not x) b)
not-surjective true = false , tt
not-surjective false = true , tt

-- For every boolean b, there is some boolean x such that (not x ≠ b)
prf₁ : (b : Bool) → Σ Bool (λ x → ¬ Eqb (not x) b)
prf₁ true = true , exfalso
prf₁ false = false , exfalso

-- not doesn't have a fixed point : there is no boolean b such that (b = not b)
¬fixedpoint-not : ¬ (Σ Bool (λ b → Eqb b (not b)))
¬fixedpoint-not (true , eq) = eq
¬fixedpoint-not (false , eq) = eq

-- Copattern matching : we can define pairs and dependent pairs by giving all components.
-- The definition
--   proj₁ p = a
--   proj₂ p = b
-- is equivalent to
--   p = a , b
curryd : (A : Set) → (B : A → Set) → (C : Set)
       → (Σ A B → C) ↔ ((a : A) → B a → C)
proj₁ (curryd A B C) f a b = f (a , b)
proj₂ (curryd A B C) f (a , b) = f a b


-- Division by 2: for every natural number n, there
-- is a natural number m such that either (n = 2*m) or (n = 2*m + 1)
2* : ℕ → ℕ
2* zero    = zero
2* (suc n) = suc (suc (2* n))

div2-helper : (n : ℕ) → Σ ℕ (λ m → Eqn n (2* m) ⊎ Eqn n (suc (2* m)))
                      → Σ ℕ (λ m → Eqn (suc n) (2* m) ⊎ Eqn (suc n) (suc (2* m)))
div2-helper n (m , inj₁ x) = m , inj₂ x
div2-helper n (m , inj₂ x) = suc m , inj₁ x

div2 : (n : ℕ) → Σ ℕ (λ m → Eqn n (2* m) ⊎ Eqn n (suc (2* m)))
div2 zero = zero , inj₁ tt
div2 (suc n) = div2-helper n (div2 n)
