module t4.gy12 where
open import lib
open import Agda.Primitive

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
--    Σ       \Sigma
--    ≡       \==

--------------------------------------------------------------------------------
--- Equality types
--------------------------------------------------------------------------------

-- ≡

-- data _≡_ {A : Type} (x : A) : (y : A) → Type where
--   refl : x ≡ x

-- Equality is reflexive
refl' : {A : Type} {x : A} → x ≡ x
refl' = refl

-- Equality is symmetric
sym : {A : Type} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- Equality is transitive
trans : {A : Type} {x y z : A}
      → x ≡ y
      → y ≡ z
      → x ≡ z
trans refl p = p

-- Equality is "substitutive"
subst : {A : Type} {x y : A} (P : A → Type)
      → x ≡ y
      → P x → P y
subst P refl d = d

-- This is also called "transport":
transport = subst

-- Equality satisfies congruence
cong : ∀ {i j} {A : Set i} {B : Set j} {x y : A} (f : A → B)
     → x ≡ y
     → f x ≡ f y
cong f refl = refl

-- This is also called "ap" (Action on Paths)
ap = cong

--------------------------------------------------------------------------------

-- True is not equal to false:
¬true≡false : ¬ (true ≡ false)
¬true≡false p = subst (λ b → f b) p tt
  where
    f : Bool → Type
    f true  = ⊤
    f false = ⊥
    -- If true ≡ false, then by subst we have f true → f false

sym≠ : {A : Type} {x y : A} → ¬ (x ≡ y) → ¬ (y ≡ x)
sym≠ p q = p (sym q)

-- Boolean equality is decidable
dec-≡-Bool : ∀ {x y : Bool} → (x ≡ y) ⊎ (¬ (x ≡ y))
dec-≡-Bool {false} {false} = inl refl
dec-≡-Bool {false} {true}  = inr (λ p → ¬true≡false (sym p))
dec-≡-Bool {true} {false}  = inr (λ p → ¬true≡false p)
dec-≡-Bool {true} {true}   = inl refl

_≟_ : Bool → Bool → Bool
false ≟ false = true
false ≟ true  = false
true  ≟ false = false
true  ≟ true  = true

-- Booleans x,y are equal iff (x ≟ y) is true.
≟-correct : ∀ {x y} → (x ≡ y) ↔ ((x ≟ y) ≡ true)
≟-correct {false} {false} = (λ _ → refl) , (λ _ → refl)
≟-correct {false} {true}  = (λ x → x) , (λ x → x)
≟-correct {true} {false}  = sym , sym
≟-correct {true} {true}   = (λ _ → refl) , (λ _ → refl)

-- If x,y : Bool and ¬ (¬ (x ≡ y)), then x ≡ y
¬¬-≡-Bool : ∀ {x y : Bool} → ¬ (¬ (x ≡ y)) → (x ≡ y)
¬¬-≡-Bool = {!!}

not : Bool → Bool
not b = if b then false else true

-- Properties of the function not
not-not : ∀ (x : Bool) → not (not x) ≡ x
not-not = {!!}

not-injective : ∀ (x y : Bool) → (not x ≡ not y) → x ≡ y
not-injective = {!!}

not-surjective : ∀ (x : Bool) → Σ Bool (λ y → not y ≡ x)
not-surjective = {!!}

--------------------------------------------------------------------------------

-- Properties of addition:

zero+ : ∀ n → zero + n ≡ n
zero+ = {!!}

+zero : ∀ n → n + zero ≡ n
+zero = {!!}

suc+ : ∀ n m → suc n + m ≡ suc (n + m)
suc+ = {!!}

+suc : ∀ n m → n + suc m ≡ suc (n + m)
+suc = {!!}

+assoc : ∀ n m k → (n + m) + k ≡ n + (m + k)
+assoc = {!!}

+comm : ∀ n m → n + m ≡ m + n
+comm = {!!}

ex1 : ∀ n m → (1 * n + 2 * m) ≡ (2 * m + 1 * n)
ex1 n m = {!!}

zero* : ∀ n → 0 * n ≡ 0
zero* = {!!}

*zero : ∀ n → n * 0 ≡ 0
*zero = {!!}

suc* : ∀ n m → (suc n) * m ≡ m + n * m
suc* = {!!}

*suc : ∀ n m → n * (suc m) ≡ n + n * m
*suc = {!!}

*comm : ∀ n m → n * m ≡ m * n
*comm = {!!}

+*dist : ∀ n m k → (n + m) * k ≡ n * k + m * k
+*dist = {!!}

*assoc : ∀ n m k → (n * m) * k ≡ n * (m * k)
*assoc zero m k = refl
*assoc (suc n) m k = trans (+*dist m (n * m) k) {!!}

--------------------------------------------------------------------------------

-- Hard bonus exercise: prove the general pigeonhole principle.

infixr 6 _∷_
data Vec (A : Type) : ℕ → Type where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

data Fin : ℕ → Type where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

_!!_ : ∀ {n A} → Vec A n → Fin n → A
[] !! ()
(x ∷ xs) !! zero  = x
(x ∷ xs) !! suc i = xs !! i

-- The function f(i,j) = if j>i then j-1 else j
punchOut : ∀ {n} {i j : Fin (suc n)} → ¬ (i ≡ j) → Fin n
punchOut = {!!}

-- Use induction on n
pigeonhole : ∀ {n} (xs : Vec (Fin n) (suc n))
           → Σ (Fin (suc n) × Fin (suc n))
               (λ { (i , j) → (xs !! i ≡ xs !! j) × ¬ (i ≡ j) })
pigeonhole = {!!}
