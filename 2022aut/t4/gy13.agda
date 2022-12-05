module t4.gy13 where
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
-- Properties of negation

-- de Morgan laws
dm1 : {X Y : Type} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
dm1 = {!!}

dm2 : {X Y : Type} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 = {!!}

dm2b : {X Y : Type} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b = {!!}

-- other properties
nocontra : {X : Type} → ¬ (X ↔ ¬ X)
nocontra = {!!}

¬¬invol₁ : {X : Type} → ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
¬¬invol₁ = {!!}

¬¬invol₂ : {X : Type} → ¬ ¬ ¬ X ↔ ¬ X
¬¬invol₂ = {!!}

nnlem : {X : Type} → ¬ ¬ (X ⊎ ¬ X)
nnlem = {!!}

nndnp : {X : Type} → ¬ ¬ (¬ ¬ X → X)
nndnp = {!!}

dec2stab : {X : Type} → (X ⊎ ¬ X) → (¬ ¬ X → X)
dec2stab = {!!}

-- ¬¬ is a monad:
¬¬-map : ∀ {A B : Type} → (A → B) → ¬ (¬ A) → ¬ (¬ B)
¬¬-map = {!!}

¬¬-return : ∀ {A : Type} → A → ¬ (¬ A)
¬¬-return = {!!}

¬¬-join : ∀ {A : Type} → ¬ ¬ (¬ ¬ A) → ¬ ¬ A
¬¬-join = ¬¬invol₁ .fst

-- Examples
e₁ : ¬ ((n : ℕ) → (n < 3) ≡ true → (n < 2) ≡ true)
e₁ = {!!}

e₂ : ¬ (Σ ℕ λ n → (n < 3) ≡ true × (3 < n) ≡ true)
e₂ = {!!}

--------------------------------------------------------------------------------

-- Properties of addition:

zero+ : ∀ n → zero + n ≡ n
zero+ = {!!}

+zero : ∀ n → n + zero ≡ n
+zero zero    = refl
+zero (suc n) = cong suc (+zero n)

suc+ : ∀ n m → suc n + m ≡ suc (n + m)
suc+ = {!!}

+suc : ∀ n m → n + suc m ≡ suc (n + m)
+suc = {!!}

+assoc : ∀ n m k → (n + m) + k ≡ n + (m + k)
+assoc = {!!}

+comm : ∀ n m → n + m ≡ m + n
+comm = {!!}

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
*assoc n m k = {!!}

_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ suc m = n * n ^ m

*one : ∀ {n} → n * 1 ≡ n
*one {zero} = refl
*one {suc n} = cong suc *one

^2-eq : ∀ {n} → n ^ 2 ≡ n * n
^2-eq {n} = cong (_*_ n) *one

_$_ : ∀ {A B} → (A → B) → A → B
f $ x = f x
infixr -1 _$_

ex1 : ∀ {x y} → (x + y) ^ 2 ≡ x ^ 2 + 2 * x * y + y ^ 2
ex1 {x} {y} = {!!}

--------------------------------------------------------------------------------
