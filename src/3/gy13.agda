module gy13 where

open import Lib hiding (_≟ℕ_)
open import Lib.Containers.List

---------------------------------------------------------
-- konstruktorok injektivitasa
------------------------------------------------------

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

∷inj1 : {A : Set}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
∷inj1 = {!!}

∷inj2 : {A : Set}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
∷inj2 = {!!}

-- prove all of the above without pattern matching on equalities!

---------------------------------------------------------
-- konstruktorok diszjunktsaga
------------------------------------------------------

n≠sucn : (n : ℕ) → n ≢ suc n
n≠sucn = {!!}

-- prove this using induction on n!
n≠sucn' : (n : ℕ) → n ≢ suc n
n≠sucn' n = {!!}

leaf≠node : ∀{f} → Tree.leaf ≢ node f
leaf≠node = {!!}

leaf≠node' : ∀{x y} → BinTree.leaf ≢ node x y
leaf≠node' = {!!}

nil≠cons : {A : Set}{x : A}{xs : List A} → [] ≢ x ∷ xs
nil≠cons = {!!}

---------------------------------------------------------
-- egyenlosegek eldonthetosege
------------------------------------------------------

_≟Bool_ : (b b' : Bool) → Dec (b ≡ b')
_≟Bool_ = {!!}

_≟ℕ_ : (n n' : ℕ) → Dec (n ≡ n')
_≟ℕ_ = {!!}

_≟BinTree_ : (t t' : BinTree) → Dec (t ≡ t')
_≟BinTree_ = {!!}

_≟List_ : {A : Set} → ({x y : A} → Dec (x ≡ y)) → {xs ys : List A} → Dec (xs ≡ ys)
_≟List_ = {!!}

-------------------------------------------
-- Típusosztályok (esetleg szabályokkal is)
-------------------------------------------

-- Eq
-- Ord
-- Semigroup
-- Monoid