open import lib

---------------------------------------------------------
-- library
------------------------------------------------------

sym : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀{i j}{A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y
subst P refl p = p

---------------------------------------------------------
-- konstruktorok injektivitasa
------------------------------------------------------

sucinj : (m n : ℕ) → suc m ≡ suc n → m ≡ n
sucinj m .m refl = refl

-- prove it without pattern matching on e! (hint: use pred)
sucinj' : (m n : ℕ) → suc m ≡ suc n → m ≡ n
sucinj' zero zero e = refl
sucinj' (suc m) (suc n) e = cong pred e

data Tree : Set where
  leaf : Tree
  node : (ℕ → Tree) → Tree

nodeinj : ∀{f g} → node f ≡ node g → f ≡ g
nodeinj refl = refl

data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree

nodeinjl : ∀{x y x' y'} → BinTree.node x y ≡ node x' y' → x ≡ x'
nodeinjl refl = refl

nodeinjr : ∀{x y x' y'} → BinTree.node x y ≡ node x' y' → y ≡ y'
nodeinjr refl = refl

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

∷inj1 : ∀{A}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
∷inj1 refl = refl

∷inj2 : ∀{A}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
∷inj2 refl = refl

-- prove all of the above without pattern matching on equalities!

---------------------------------------------------------
-- konstruktorok diszjunktsaga
------------------------------------------------------

true≠false : ¬ (true ≡ false)
true≠false ()

-- prove this without pattern matching in this function on e! (use subst!)
true≠false' : ¬ (true ≡ false)
true≠false' e = subst (λ {true → ⊤; false → ⊥}) e tt

zero≠sucn : ∀{n} → ¬ (zero ≡ suc n)
zero≠sucn ()

n≠sucn : ∀ n → ¬ (n ≡ suc n)
n≠sucn n ()

-- prove this using induction on n!
n≠sucn' : ∀ n → ¬ (n ≡ suc n)
n≠sucn' zero x = subst (λ {zero → ⊤; (suc n) → ⊥}) x tt
n≠sucn' (suc n) x = n≠sucn' n (cong pred x)

leaf≠node : ∀{f} → ¬ (Tree.leaf ≡ node f)
leaf≠node ()

leaf≠node' : ∀{x y} → ¬ (BinTree.leaf ≡ node x y)
leaf≠node' x = subst (λ {leaf → ℕ; (node a b) → ⊥}) x 42

nil≠cons : ∀{A}{x : A}{xs} → ¬ ([] ≡ x ∷ xs)
nil≠cons x = subst (λ {[] → ℕ; (a ∷ as) → ⊥}) x zero

---------------------------------------------------------
-- egyenlosegek eldonthetosege
------------------------------------------------------

Dec : Set → Set
Dec A = A ⊎ ¬ A

_≟Bool_ : (b b' : Bool) → Dec (b ≡ b')
false ≟Bool false = inl refl
false ≟Bool true = inr λ ()
true ≟Bool false = inr λ ()
true ≟Bool true = inl refl

_≟ℕ_ : (n n' : ℕ) → Dec (n ≡ n')
zero ≟ℕ zero = inl refl
zero ≟ℕ suc n' = inr λ ()
suc n ≟ℕ zero = inr λ ()
suc n ≟ℕ suc n' = case (n ≟ℕ n') (λ x → inl (cong suc x)) λ x → inr λ x₁ → x (cong pred x₁)

-- is equality for Tree decidable?

_≟BinTree_ : (t t' : BinTree) → Dec (t ≡ t')
leaf ≟BinTree leaf = inl refl
leaf ≟BinTree node t' t'' = inr λ ()
node t t₁ ≟BinTree leaf = inr λ ()
node t t₁ ≟BinTree node t' t'' =
  case (t ≟BinTree t')
    (λ {refl → case (t₁ ≟BinTree t'')
      (λ {refl → inl refl})
      λ x → inr λ x₁ → x (nodeinjr x₁)})
    λ x → inr λ x₁ → x (nodeinjl x₁)

_≟List_ : {A : Set} → ({x y : A} → Dec (x ≡ y)) → {xs ys : List A} → Dec (xs ≡ ys)
_≟List_ = {!!}
