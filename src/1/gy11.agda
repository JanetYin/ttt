module gy11 where

open import lib
open import proofs

---------------------------------------------------------
-- konstruktorok injektivitasa
------------------------------------------------------

sucinj'' : (m n : ℕ) → suc m ≡ suc n → m ≡ n
sucinj'' = {!!}

-- prove it without pattern matching on e! (hint: use pred)
sucinj' : (m n : ℕ) → suc m ≡ suc n → m ≡ n
sucinj' m n e = {!!}

data Tree : Set where
  leaf : Tree
  node : (ℕ → Tree) → Tree

nodeinj : ∀{f g} → node f ≡ node g → f ≡ g
nodeinj = {!!}

data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree

nodeinjl : ∀{x y x' y'} → BinTree.node x y ≡ node x' y' → x ≡ x'
nodeinjl = {!!}

nodeinjr : ∀{x y x' y'} → BinTree.node x y ≡ node x' y' → y ≡ y'
nodeinjr = {!!}

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

∷inj1 : ∀{A}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
∷inj1 = {!!}

∷inj2 : ∀{A}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
∷inj2 = {!!}

-- ezeket egyszerre is fel lehet írni nyugodtan
∷inj : ∀{A}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → {!   !}
∷inj = {!   !}

-- prove all of the above without pattern matching on equalities!

---------------------------------------------------------
-- konstruktorok diszjunktsaga
------------------------------------------------------

true≠false : ¬ (true ≡ false)
true≠false = {!!}

-- prove this without pattern matching in this function on e! (use subst!)
true≠false' : ¬ (true ≡ false)
true≠false' e = {!!}

zero≠sucn : ∀{n} → ¬ (zero ≡ suc n)
zero≠sucn = {!!}

n≠sucn : ∀ n → ¬ (n ≡ suc n)
n≠sucn = {!!}

-- prove this using induction on n!
n≠sucn' : ∀ n → ¬ (n ≡ suc n)
n≠sucn' n = {!!}

leaf≠node : ∀{f} → ¬ (Tree.leaf ≡ node f)
leaf≠node = {!!}

leaf≠node' : ∀{x y} → ¬ (BinTree.leaf ≡ node x y)
leaf≠node' = {!!}

nil≠cons : ∀{A}{x : A}{xs} → ¬ ([] ≡ x ∷ xs)
nil≠cons = {!!}

---------------------------------------------------------
-- egyenlosegek eldonthetosege
------------------------------------------------------

Dec : ∀{i} → Set i → Set i
Dec A = A ⊎ ¬ A

_≟Bool_ : (b b' : Bool) → Dec (b ≡ b')
_≟Bool_ = {!!}

_≟ℕ_ : (n n' : ℕ) → Dec (n ≡ n')
_≟ℕ_ = {!!}

-- is equality for Tree decidable?

_≟BinTree_ : (t t' : BinTree) → Dec (t ≡ t')
_≟BinTree_ = {!!}

_≟List_ : {A : Set} → ({x y : A} → Dec (x ≡ y)) → {xs ys : List A} → Dec (xs ≡ ys)
_≟List_ = {!!}

-------------------------------------------
-- injektív függvények
-------------------------------------------

+injl : {n m k : ℕ} → n + m ≡ n + k → m ≡ k
+injl = {!   !}

+injr : {n m k : ℕ} → n + m ≡ k + m → n ≡ k
+injr = {!   !}

*injr : {n m k : ℕ} → n * suc m ≡ k * suc m → n ≡ k
*injr = {!   !}

*injl : {n m k : ℕ} → suc n * m ≡ suc n * k → m ≡ k
*injl = {!   !}

-------------------------------------------
-- nem egyenlőségek
-------------------------------------------

task1 : ¬ ((n : ℕ) → n ≡ 3)
task1 = {!   !}

task2 : {n : ℕ} → n ≡ 3 → n ≢ 10
task2 = {!   !}

≢notTrans : ∀{i} → ¬ ({A : Set i}{a b c : A} → a ≢ b → b ≢ c → a ≢ c)
≢notTrans = {!   !}

≢notReflexive : ∀{i}{A : Set i}{a : A} → ¬ (a ≢ a)
≢notReflexive = {!   !}

task3 : ⊤ ≢ ⊤ ⊎ ⊤
task3 = {!   !}