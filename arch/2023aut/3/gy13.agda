module gy13 where

open import Lib hiding (_≟ℕ_)
open import Lib.Containers.List

---------------------------------------------------------
-- konstruktorok injektivitasa
------------------------------------------------------

data Tree : Set where
  leaf : Tree
  node : (ℕ → Tree) → Tree

removeNode : Tree → (ℕ → Tree)
removeNode leaf _ = leaf
removeNode (node x) = x

nodeinj : ∀{f g} → node f ≡ node g → f ≡ g
nodeinj e = cong removeNode e

data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree

takeNodeL : BinTree → BinTree
takeNodeL leaf = leaf
takeNodeL (node l r) = l

nodeinjl : ∀{x y x' y'} → BinTree.node x y ≡ node x' y' → x ≡ x'
nodeinjl = cong takeNodeL

takeNodeR : BinTree → BinTree
takeNodeR leaf = leaf
takeNodeR (node l r) = r

nodeinjr : ∀{x y x' y'} → BinTree.node x y ≡ node x' y' → y ≡ y'
nodeinjr = cong takeNodeR

head' : {A : Set} → A → List A → A
head' a [] = a
head' _ (x ∷ xs) = x

∷inj1 : {A : Set}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
∷inj1 {x = x} = cong (head' x)

tail' : {A : Set} → List A → List A
tail' [] = []
tail' (x ∷ xs) = xs

∷inj2 : {A : Set}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
∷inj2 = cong tail'

-- prove all of the above without pattern matching on equalities!

---------------------------------------------------------
-- konstruktorok diszjunktsaga
------------------------------------------------------

n≠sucn : (n : ℕ) → n ≢ suc n
n≠sucn n ()

-- prove this using induction on n!
n≠sucn' : (n : ℕ) → n ≢ suc n
n≠sucn' zero e = subst P e tt where
  P : ℕ → Set
  P zero = ⊤
  P (suc _) = ⊥
n≠sucn' (suc n) e = n≠sucn' n (suc-injective e)

leaf≠node : ∀{f} → Tree.leaf ≢ node f
leaf≠node e = subst P e tt where
  P : Tree → Set
  P leaf = ⊤
  P (node x) = ⊥

leaf≠node' : ∀{x y} → BinTree.leaf ≢ node x y
leaf≠node' e = subst P e tt where
  P : BinTree → Set
  P leaf = ⊤
  P (node _ _) = ⊥

nil≠cons : {A : Set}{x : A}{xs : List A} → [] ≢ x ∷ xs
nil≠cons e = subst P e tt where
  P : {A : Set} → List A → Set
  P [] = ⊤
  P (_ ∷ _) = ⊥

---------------------------------------------------------
-- egyenlosegek eldonthetosege
------------------------------------------------------

_≟Bool_ : (b b' : Bool) → Dec (b ≡ b')
false ≟Bool false = inl refl
false ≟Bool true = inr λ ()
true ≟Bool false = inr λ ()
true ≟Bool true = inl refl

_≟ℕ_ : (n n' : ℕ) → Dec (n ≡ n')
zero ≟ℕ zero    = inl refl
zero ≟ℕ suc n'  = inr (λ ())
suc n ≟ℕ zero   = inr (λ ())
suc n ≟ℕ suc n' with n ≟ℕ n'
... | inl a = inl (cong suc a)
... | inr b = inr λ e → b (suc-injective e)

_≟BinTree_ : (t t' : BinTree) → Dec (t ≡ t')
leaf ≟BinTree leaf = inl refl
leaf ≟BinTree node t' t'' = inr (λ ())
node t t₁ ≟BinTree leaf = inr (λ ())
node l r ≟BinTree node l' r' with l ≟BinTree l' | r ≟BinTree r'
... | inr b | e2 = inr λ e → b (nodeinjl e)
... | inl a | inl a' = inl (cong₂ node a a')
... | inl a | inr b = inr λ e → b (nodeinjr e)

_>_≟List_ : {A : Set} → ((a b : A) → Dec (a ≡ b)) → (xs ys : List A) → Dec (xs ≡ ys)
f > [] ≟List [] = inl refl
f > [] ≟List (x ∷ ys) = inr (λ ())
f > (x ∷ xs) ≟List [] = inr (λ ())
f > (x ∷ xs) ≟List (y ∷ ys) with f x y | f > xs ≟List ys
... | inr b | e2 = inr λ e → b (∷inj1 e)
... | inl a | inl a' = inl (cong₂ _∷_ a a')
... | inl a | inr b = inr λ e → b (∷inj2 e)