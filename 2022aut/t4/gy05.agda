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

assoc⊎₁ : {A B C : Type} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
assoc⊎₁ (inl (inl a)) = inl a
assoc⊎₁ (inl (inr b)) = inr (inl b)
assoc⊎₁ (inr c) = inr (inr c)

assoc⊎₂ : {A B C : Type} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
assoc⊎₂ (inl a) = inl (inl a)
assoc⊎₂ (inr (inl b)) = inl (inr b)
assoc⊎₂ (inr (inr c)) = inr c

assoc⊎ : {A B C : Type} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C)
assoc⊎ = assoc⊎₁ , assoc⊎₂

idl⊎₁ : {A : Type} → ⊥ ⊎ A → A
idl⊎₁ (inl x) = exfalso x
idl⊎₁ (inr x) = x

idl⊎₂ : {A : Type} → A → ⊥ ⊎ A
idl⊎₂ = inr

idl⊎ : {A : Type} → ⊥ ⊎ A ↔ A
idl⊎ = idl⊎₁ , idl⊎₂

-- Corresponds to   n + 0 = n
idr⊎₁ : {A : Type} → A ⊎ ⊥ → A
idr⊎₁ (inl a)  = a
idr⊎₁ (inr e⊥) = exfalso e⊥
-- idr⊎₁ (inr ())
--                 or pattern match on e⊥

idr⊎₂ : {A : Type} → A → A ⊎ ⊥
idr⊎₂ a = inl a

idr⊎ : {A : Type} → A ⊎ ⊥ ↔ A
idr⊎ = idr⊎₁ , idr⊎₂

-- Alternative:
-- idr⊎' : {A : Type} → A ⊎ ⊥ ↔ A
-- idr⊎' .fst = {!!}
-- idr⊎' .snd = {!!}

comm⊎ : {A B : Type} → A ⊎ B ↔ B ⊎ A
comm⊎ = (λ x → case x inr inl) , (λ x → case x inr inl)

-- (×, ⊤) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc× : {A B C : Type} → (A × B) × C ↔ A × (B × C)
assoc× = (λ ((a , b) , c) → (a , (b , c)))
       , (λ p → ((fst p , fst (snd p)) , snd (snd p)))

idl× : {A : Type} → ⊤ × A ↔ A
idl× = snd , (λ a → tt , a)

idr× : {A : Type} → A × ⊤ ↔ A
idr× = fst , (λ a → a , tt)

-- ⊥ is a null element

-- null× : {A : Type} → A × ⊥ ↔ ⊥
-- null× = {!!}

-- distributivity of × and ⊎

dist₁ : {A B C : Type} → A × (B ⊎ C) → (A × B) ⊎ (A × C)
dist₁ (a , inl b) = inl (a , b)
dist₁ (a , inr c) = inr (a , c)

dist₂ : {A B C : Type} → (A × B) ⊎ (A × C) → A × (B ⊎ C)
dist₂ (inl (a , b)) = a , inl b
dist₂ (inr (a , c)) = a , inr c

dist : {A B C : Type} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
dist = dist₁ , dist₂

-- exponentiation laws

curry' : ∀{A B C : Type} → (A × B → C) ↔ (A → B → C)
curry' = (λ f a b → f (a , b))
       , (λ f p → f (fst p) (snd p))

⊎×→ : {A B C D : Type} → ((A ⊎ B) → C) ↔ (A → C) × (B → C)
⊎×→ = (λ f → (λ a → f (inl a)) , (λ b → f (inr b)))
    , (λ (fa , fb) aorb → case aorb fa fb)

law^0 : {A : Type} → (⊥ → A) ↔ ⊤
law^0 = (λ _ → tt) , (λ _ → exfalso)

law^1 : {A : Type} → (⊤ → A) ↔ A
law^1 = (λ f → f tt) , (λ a _ → a)

law1^ : {A : Type} → (A → ⊤) ↔ ⊤
law1^ = (λ _ → tt) , (λ _ _ → tt)

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
