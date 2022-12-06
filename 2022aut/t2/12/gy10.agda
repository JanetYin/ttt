module gy10 where
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

-- (2 + 2) = 4
-- (suc n + m) = (suc (n + m))

-- Agda doesn't know: (suc n + m) = (n + suc m)
-- this will come later
-- data _≡_ {A : Set} (x : A) : A → Set where
--   refl : x ≡ x

-- Equality is reflexive
refl' : {A : Set} {x : A} → x ≡ x
refl' = refl

-- Equality is symmetric
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- Equality is transitive
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

-- Equality is "substitutive"
subst : {A : Set} {x y : A} (P : A → Set)
      → x ≡ y
      → P x → P y
subst P refl Px = Px

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
ex1 : {A : Set} {a b c d : A}
    → a ≡ b
    → c ≡ b
    → c ≡ d
    → a ≡ d
ex1 = {!!}

ex2 : {A : Set} (f : A → A) {x y : A}
    → x ≡ y
    → f y ≡ f x
ex2 = {!!}



-- cong f p : f x ≡ f y
-- sym (cong f p) : f y ≡ f x
-- trans

ex3 : {A : Set} (f : A → A) (g : A → A)
    → ((x : A) → f (g x) ≡ g (f x))
    → ((a : A) → f (f (g a)) ≡ g (f (f a)))
ex3 f g hp a
  = {!!}

--------------------------------------------------------------------------------

-- True is not equal to false:
¬true≡false : ¬ (true ≡ false)
-- ¬true≡false : (true ≡ false) → ⊥
¬true≡false p = subst (λ b → f b) p tt
  where
    f : Bool → Set
    f true  = ⊤
    f false = ⊥
    -- If true ≡ false, then by subst we have f true → f false

-- or as we have learned:
¬true≡false' : ¬ (true ≡ false)
¬true≡false' ()

-- Boolean equality is decidable
dec-≡-Bool : ∀ {x y : Bool} → (x ≡ y) ⊎ (¬ (x ≡ y))
dec-≡-Bool {false} {false} = inl refl
dec-≡-Bool {true}  {false} = inr ¬true≡false -- ¬true≡false
dec-≡-Bool {false} {true}  = inr {!!} -- ¬true≡false + sym
dec-≡-Bool {true}  {true}  = inl refl

-- Definition of _==_ (imported from lib.agda)
_==b_ : Bool → Bool → Bool
false ==b false = true
false ==b true = false
true ==b false = false
true ==b true = true

-- Booleans x,y are equal iff (x ==b y) is true.
-- (this means the _==b_ operation has in some sense a similar meaning to ≡)
==b-correct : ∀ {x y : Bool} → (x ≡ y) ↔ ((x ==b y) ≡ true)
==b-correct {b1} {b2} = {!!}

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

--prove it first mathematically
--and use the earlier theorems!
+comm : ∀ n m → n + m ≡ m + n
+comm zero m = sym (+zero m)
+comm (suc n) m = {!!}

----------

-- Negative proofs

lemma0 : ¬ (0 ≡ 1)   --might have to write as a helper function
lemma0 = λ {()}
--or lemma0 (); but this cannot be written inline

lemma1 : ¬ ((n : ℕ) → (n ≡ 0) → (n ≡ 1))
lemma1 = {!!}

lemma2 : ¬ (Σ ℕ (λ n → (n ≡ 0) × (n ≡ 1)))
lemma2 = {!!}

lemma3 : ¬ ((n : ℕ) → ¬ (n ≡ 0) → (n ≡ 1))
lemma3 f = {!f 2 ?!}

lemma4 : ¬ ((n m : ℕ) → (n ≡ m) → ¬ (n ≡ 2 * m))
lemma4 = {!!}

lemma5 : (n : ℕ) → ¬ (suc n ≡ n)
lemma5 = {!!}

--# NOTE: this is important!
-- use with
-- it can recognize (suc sth ≡ sth) is empty, but not much more
lemma22 : (n : ℕ) → ¬ ((3 + n) ≡ (n + 1))
lemma22 zero = λ {()}
lemma22 (suc n) eq with trans eq (trans ((cong suc (+suc n 0))) (cong (λ n → suc (suc n)) (+zero n)))
lemma22 (suc n) eq | ()

--------------------------------------------------------------------------------

-- Hard bonus exercise: prove the general pigeonhole principle.

infixr 6 _∷_
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

_!!_ : ∀ {n A} → Vec A n → Fin n → A
[] !! ()
(x ∷ xs) !! zero  = x
(x ∷ xs) !! suc i = xs !! i

-- The function f(i,j) = if j>i then j-1 else j
punchOut : ∀ {n} (i j : Fin (suc n)) → ¬ (i ≡ j) → Fin n
punchOut zero zero n0eq0 = exfalso (n0eq0 refl)
punchOut _ (suc j) _ = j
punchOut (suc i) _ _ = i

dec-≡-ℕ : {n m : ℕ} → n ≡ m ⊎ ¬ (n ≡ m)
dec-≡-ℕ {zero} {zero} = inl refl
dec-≡-ℕ {zero} {suc m} = inr (λ ())
dec-≡-ℕ {suc n} {zero} = inr (λ ())
dec-≡-ℕ {suc n} {suc m} with dec-≡-ℕ {n} {m}
dec-≡-ℕ {suc n} {suc m}  | inl refl = inl refl
dec-≡-ℕ {suc n} {suc m}  | inr neq = inr {!!}
  

{-
-- Use induction on n
pigeonhole : ∀ {n} (xs : Vec (Fin n) (suc n))
           → Σ (Fin (suc n) × Fin (suc n))
               (λ { (i , j) → (xs !! i ≡ xs !! j) × ¬ (i ≡ j) })
pigeonhole {zero} xs = Finzeroelim (xs !! zero)
  where
  Finzeroelim : ∀ {i} {A : Set i} → Fin zero → A
  Finzeroelim ()
pigeonhole {suc n} xs with dec-≡-Nat {xs !! zero} {xs !! suc zero}
pigeonhole {suc n} xs   | inl refl = ?
pigeonhole {suc n} xs   | inr neq = ?
-}
