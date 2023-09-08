module gy11 where

open import lib
open import proofs

---------------------------------------------------------
-- konstruktorok injektivitasa
------------------------------------------------------

sucinj'' : (m n : ℕ) → suc m ≡ suc n → m ≡ n
sucinj'' m .m refl = refl

-- prove it without pattern matching on e! (hint: use pred)
sucinj' : (m n : ℕ) → suc m ≡ suc n → m ≡ n
sucinj' m n e = cong pred e

data Tree : Set where
  leaf : Tree
  node : (ℕ → Tree) → Tree

getNode : Tree → (ℕ → Tree)
getNode leaf = λ _ → leaf
getNode (node x) = x

nodeinj : ∀{f g} → node f ≡ node g → f ≡ g
nodeinj e = cong getNode e

data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree

left : BinTree → BinTree
left leaf = leaf
left (node l r) = l

right : BinTree → BinTree
right leaf = leaf
right (node l r) = r

nodeinjl : ∀{x y x' y'} → BinTree.node x y ≡ node x' y' → x ≡ x'
nodeinjl = cong left

nodeinjr : ∀{x y x' y'} → BinTree.node x y ≡ node x' y' → y ≡ y'
nodeinjr = cong right

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

getInl : {A : Set} → A ⊎ A → A
getInl (inl x) = x
getInl (inr x) = x

inl-inj : {A : Set}{x y : A} → inl x ≡ inl y → x ≡ y
inl-inj = cong getInl

∷inj1 : ∀{A}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
∷inj1 {_} {x} e = cong (λ {[] → x; (l ∷ ls) → l}) e

tail : {A : Set} → List A → List A
tail [] = []
tail (_ ∷ xs) = xs

∷inj2 : ∀{A}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
∷inj2 = cong tail

-- ezeket egyszerre is fel lehet írni nyugodtan
∷inj : ∀{A}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → (x ≡ y) × (xs ≡ ys)
∷inj e = ∷inj1 e , ∷inj2 e

-- prove all of the above without pattern matching on equalities!

---------------------------------------------------------
-- konstruktorok diszjunktsaga
------------------------------------------------------

true≠false : ¬ (true ≡ false)
true≠false ()

-- prove this without pattern matching in this function on e! (use subst!)
true≠false' : ¬ (true ≡ false)
true≠false' e = subst P e tt where
  P : Bool → Set
  P false = ⊥
  P true = ⊤

zero≠sucn : ∀{n} → ¬ (zero ≡ suc n)
zero≠sucn e = subst P e tt where
  P : ℕ → Set
  P zero = ⊤
  P (suc _) = ⊥

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

_≟BinTree_ : (t t' : BinTree) → Dec (t ≡ t')
_≟BinTree_ = {!   !}

_≟List_ : {A : Set} → (xs ys : List A) → {f : (x y : A) → Dec (x ≡ y)} → Dec (xs ≡ ys)
_≟List_ = {!   !}

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

task3 : ⊤ ≢ (⊤ ⊎ ⊤)
task3 eq = {! eq  !}