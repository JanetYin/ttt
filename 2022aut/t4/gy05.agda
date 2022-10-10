module t4.gy05 where
open import lib hiding (_<_)

-- List of unicode symbols:
--    →       \to
--            \rightarrow
--    ℕ       \bN           'b'lackboard 'N', there is also \bZ for ℤ, etc
--    λ       \Gl           'G'reek 'l', there is also \GG for Γ, etc
--            \lambda
--    ×       \times
--    ⊎       \u+
--    ⊤       \top
--    ⊥       \bot
--    ↔       \lr
--    ₁       \_1
--    ₐ       \_a
--    ¹       \^1

--- Algebraic laws

-- (⊎, ⊥) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc⊎ : {A B C : Set} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C)
assoc⊎ = {!!}

idl⊎ : {A : Set} → ⊥ ⊎ A ↔ A
idl⊎ = {!!}

idr⊎ : {A : Set} → A ⊎ ⊥ ↔ A
idr⊎ = {!!}

comm⊎ : {A B : Set} → A ⊎ B ↔ B ⊎ A
comm⊎ = {!!}

-- (×, ⊤) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc× : {A B C : Set} → (A × B) × C ↔ A × (B × C)
assoc× = {!!}

idl× : {A : Set} → ⊤ × A ↔ A
idl× = {!!}

idr× : {A : Set} → A × ⊤ ↔ A
idr× = {!!}

-- ⊥ is a null element

null× : {A : Set} → A × ⊥ ↔ ⊥
null× = {!!}

-- distributivity of × and ⊎

dist : {A B C : Set} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
dist = {!!}

-- exponentiation laws

curry : ∀{A B C : Set} → (A × B → C) ↔ (A → B → C)
curry = {!!}

⊎×→ : {A B C D : Set} → ((A ⊎ B) → C) ↔ (A → C) × (B → C)
⊎×→ = {!!}

law^0 : {A : Set} → (⊥ → A) ↔ ⊤
law^0 = {!!}

law^1 : {A : Set} → (⊤ → A) ↔ A
law^1 = {!!}

law1^ : {A : Set} → (A → ⊤) ↔ ⊤
law1^ = {!!}

--- Definitions by recursion on natural numbers

-- The type ℕ of natural numbers is a datatype with two constructors:
-- data ℕ : Type where
--   zero : ℕ
--   suc  : ℕ → ℕ   -- suc n is the successor of n, i.e. n+1

example-three : 3 ≡ suc (suc (suc zero)); example-three = refl

-- Recursive definitions can be defined using pattern matching:

double : ℕ → ℕ
double zero    = zero
double (suc n) = suc (suc (double n))

double-test : double 10 ≡ 20; double-test = refl

-- Only terminating definitions are allowed.
-- Try to uncomment the following definition:
-- bad : ℕ → ℕ
-- bad zero    = zero
-- bad (suc n) = bad (n + n)

-- Addition and multiplication are defined by recursion.

-- _+_
add : ℕ → ℕ → ℕ
add n m = {!!}

-- _*_
mult : ℕ → ℕ → ℕ
mult n m = {!!}

-- The fibonacci sequence
--   fib 0 = fib 1 = 1
--   fib n = fib (n-1) + fib (n-2)  when  n ≥ 2
fib : ℕ → ℕ
fib = {!!}

fib-test₁ : fib 1 ≡ 1; fib-test₁ = refl
fib-test₂ : fib 2 ≡ 2; fib-test₂ = refl
fib-test₃ : fib 3 ≡ 3; fib-test₃ = refl
fib-test₄ : fib 4 ≡ 5; fib-test₄ = refl

min : ℕ → ℕ → ℕ
min = {!!}

_<_ : ℕ → ℕ → Bool
_<_ = {!!}

-- (There are other exercises in ../gy04-datatypes.agda)
