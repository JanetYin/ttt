open import Lib hiding (_≟ℕ_)
open import Lib.Containers.List

---------------------------------------------------------
-- konstruktorok injektivitasa
------------------------------------------------------

sucinj : (m n : ℕ) → ℕ.suc m ≡ suc n → m ≡ n
sucinj m .m refl = refl

-- prove it without pattern matching on e! (hint: use pred')
sucinj' : (m n : ℕ) → ℕ.suc m ≡ suc n → m ≡ n
sucinj' m n x = cong pred' x

data Tree : Set where
  leaf : Tree
  node : (ℕ → Tree) → Tree

nodeinj : ∀{f g} → node f ≡ node g → f ≡ g
nodeinj refl = refl

nodeinj' : ∀{f g} → node f ≡ node g → f ≡ g
nodeinj' x = cong (λ where leaf → λ _ → leaf
                           (node x) → x) x

data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree

nodeinjl : ∀{x y x' y'} → BinTree.node x y ≡ node x' y' → x ≡ x'
nodeinjl x = cong (λ where leaf → leaf
                           (node t t₁) → t) x

nodeinjr : ∀{x y x' y'} → BinTree.node x y ≡ node x' y' → y ≡ y'
nodeinjr x = cong (λ where leaf → leaf; (node t t₁) → t₁) x

∷inj1 : {A : Set}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
∷inj1 refl = refl

∷inj2 : {A : Set}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
∷inj2 refl = refl

-- prove all of the above without pattern matching on equalities!

---------------------------------------------------------
-- konstruktorok diszjunktsaga
------------------------------------------------------

true≠false : true ≢ false
true≠false ()

-- prove this without pattern matching in this function on e! (use subst!)
true≠false' : true ≢ false
true≠false' e = subst (λ where false → ⊥
                               true → ⊤) e tt

zero≠sucn : {n : ℕ} → zero ≢ ℕ.suc n
zero≠sucn x = subst (λ where zero → ⊤
                             (suc n) → ⊥) x tt

n≠sucn : (n : ℕ) → n ≢ suc n
n≠sucn zero x = zero≠sucn x
n≠sucn (suc n) x = n≠sucn n (cong pred' x)

-- prove this using induction on n!
n≠sucn' : (n : ℕ) → n ≢ suc n
n≠sucn' n ()

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
false ≟Bool false = inl refl
false ≟Bool true = inr (λ x → true≠false (sym x))
true ≟Bool false = inr (λ x → true≠false x)
true ≟Bool true = inl refl

_≟ℕ_ : (n n' : ℕ) → Dec (n ≡ n')
zero ≟ℕ zero = inl refl
zero ≟ℕ suc n' = inr (λ x → zero≠sucn x)
suc n ≟ℕ zero = inr λ x → zero≠sucn (sym x)
suc n ≟ℕ suc n' = case (n ≟ℕ n')
  (λ x → inl (cong suc x))
  λ x → inr λ x₁ → x (cong pred' x₁)

-- is equality for Tree decidable?

_≟BinTree_ : (t t' : BinTree) → Dec (t ≡ t')
leaf ≟BinTree leaf = inl refl
leaf ≟BinTree node t' t'' = inr λ x → leaf≠node' x
node t t₁ ≟BinTree leaf = inr λ x → leaf≠node' (sym x)
node t t₁ ≟BinTree node t' t'' = case (t ≟BinTree t')
  (λ where refl → case (t₁ ≟BinTree t'') (λ where refl → inl refl) λ x → inr λ x₁ → x (nodeinjr x₁))
  λ x → inr λ x₁ → x (nodeinjl x₁)

_≟List_ : {A : Set} → ({x y : A} → Dec (x ≡ y)) → {xs ys : List A} → Dec (xs ≡ ys)
_≟List_ = {!!}
 