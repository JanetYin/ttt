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

pred : ℕ → ℕ
pred 0 = 0
pred (suc n) = n

---------------------------------------------------------
-- konstruktorok injektivitasa
------------------------------------------------------

sucinj : (m n : ℕ) → suc m ≡ suc n → m ≡ n
sucinj m n refl = refl

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

invnode : BinTree → (BinTree × BinTree)
invnode leaf = leaf , leaf
invnode (node x x₁) = x , x₁

nodeinjr : ∀{x y x' y'} → BinTree.node x y ≡ node x' y' → y ≡ y'
nodeinjr x = cong (λ y → snd (invnode y)) x

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

∷inj1 : ∀{A}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
∷inj1 = {!!}

∷inj2 : ∀{A}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
∷inj2 = {!!}

-- prove all of the above without pattern matching on equalities!

---------------------------------------------------------
-- konstruktorok diszjunktsaga
------------------------------------------------------

true≠false : ¬ (true ≡ false)
true≠false true≡false = subst (λ { false → ⊥ ; true → ⊤}) true≡false tt

-- prove this without pattern matching in this function on e! (use subst!)
true≠false' : ¬ (true ≡ false)
true≠false' ()

zero≠sucn : ∀{n} → ¬ (zero ≡ suc n)
zero≠sucn ()

n≠sucn : ∀ n → ¬ (n ≡ suc n)
n≠sucn zero x = subst (λ { zero → ⊤ ; (suc n) → ⊥}) x tt
n≠sucn (suc n) x = n≠sucn n (cong pred x)

-- prove this using induction on n!
n≠sucn' : ∀ n → ¬ (n ≡ suc n)
n≠sucn' zero ()
n≠sucn' (suc n) ()

leaf≠node : ∀{f} → ¬ (Tree.leaf ≡ node f)
leaf≠node = {!!}

leaf≠node' : ∀{x y} → ¬ (BinTree.leaf ≡ node x y)
leaf≠node' = {!!}

nil≠cons : ∀{A}{x : A}{xs} → ¬ ([] ≡ x ∷ xs)
nil≠cons = {!!}

---------------------------------------------------------
-- egyenlosegek eldonthetosege
------------------------------------------------------
-- ⊤ = \top
-- ⊥ = \bot


Dec : Set → Set
Dec A = A ⊎ ¬ A

_≟Bool_ : (b b' : Bool) → Dec (b ≡ b')
_≟Bool_ = {!!}

_≟ℕ_ : (n n' : ℕ) → Dec (n ≡ n')
_≟ℕ_ = {!!}

-- is equality for Tree decidable?

_≟BinTree_ : (t t' : BinTree) → Dec (t ≡ t')
leaf ≟BinTree leaf = {!!}
leaf ≟BinTree node t' t'' = {!!}
node t t₁ ≟BinTree leaf = {!!}
node t t₁ ≟BinTree node t' t'' with (t ≟BinTree t')
... | x with (t₁ ≟BinTree t'')
(node t t₁ ≟BinTree node t' t'') | inl x | inl x₁ = {!!}
(node t t₁ ≟BinTree node t' t'') | inl x | inr x₁ = {!!}
(node t t₁ ≟BinTree node t' t'') | inr x | inl x₁ = {!!}
(node t t₁ ≟BinTree node t' t'') | inr x | inr x₁ = {!!}

_≟List_ : {A : Set} → ({x y : A} → Dec (x ≡ y)) → {xs ys : List A} → Dec (xs ≡ ys)
_≟List_ = {!!}

lmao : ¬ (⊤ ⊎ ⊤ ⊎ ⊤ ≡ Bool)
lmao = {!!}


weird : ¬ ((n : ℕ) → 3 + n ≡ 2)
weird x with x 4
... | ()

weird2 : ¬ ((n k a : ℕ) → a * n ≡ a * k → n ≡ k)
weird2 x with x 0 1 0 refl
... | ()
