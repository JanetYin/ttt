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

_≡⟨_⟩_ : ∀{i}{A : Set i}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = trans p q

_∎ : ∀{i}{A : Set i}(x : A) → x ≡ x
_ ∎ = refl

infixr 2 _≡⟨_⟩_
infix 3 _∎

---------------------------------------------------------
-- konstruktorok injektivitasa
------------------------------------------------------

sucinj : (m n : ℕ) → suc m ≡ suc n → m ≡ n
sucinj = {!!}

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

Dec : Set → Set
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
