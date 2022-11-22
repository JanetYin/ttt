module t4.gy11 where
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

-- data _≡_ {A : Type} (x : A) : A → Type where
--   refl : x ≡ x

-- Equality is reflexive
refl' : {A : Type} {x : A} → x ≡ x
refl' = refl

-- Equality is symmetric
sym : {A : Type} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- Equality is transitive
trans : {A : Type} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
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

-- Prove the following equalities using refl, sym, trans and/or cong !
ex1 : {A : Type} {a b c d : A}
    → a ≡ b
    → c ≡ b
    → c ≡ d
    → a ≡ d
ex1 = {!!}

ex2 : {A : Type} (f : A → A) {x y : A}
    → x ≡ y
    → f y ≡ f x
ex2 = {!!}

ex3 : {A : Type} (f : A → A) (g : A → A)
    → (∀ x → f (g x) ≡ g (f x))
    → (∀ a → f (f (g a)) ≡ g (f (f a)))
ex3 = {!!}

--------------------------------------------------------------------------------

-- True is not equal to false:
¬true≡false : ¬ (true ≡ false)
¬true≡false p = subst (λ b → f b) p tt
  where
    f : Bool → Type
    f true  = ⊤
    f false = ⊥
    -- If true ≡ false, then by subst we have f true → f false

-- Boolean equality is decidable
dec-≡-Bool : ∀ {x y : Bool} → (x ≡ y) ⊎ (¬ (x ≡ y))
dec-≡-Bool = {!!}

_≟_ : Bool → Bool → Bool
false ≟ false = true
false ≟ true  = false
true  ≟ false = false
true  ≟ true  = true

-- Booleans x,y are equal iff (x ≟ y) is true.
≟-correct : ∀ {x y} → (x ≡ y) ↔ ((x ≟ y) ≡ true)
≟-correct = {!!}

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
