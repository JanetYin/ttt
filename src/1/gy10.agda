open import Lib hiding (_≟ℕ_)
open import Lib.Containers.List

---------------------------------------------------------
-- konstruktorok injektivitasa
------------------------------------------------------

sucinj : (m n : ℕ) → ℕ.suc m ≡ suc n → m ≡ n
sucinj m .m refl = refl

-- prove it without pattern matching on e! (hint: use pred)
sucinj' : (m n : ℕ) → ℕ.suc m ≡ suc n → m ≡ n
sucinj' m n e = subst (\ y -> (m ≡ pred' y)) e refl

data Tree : Set where
  leaf : Tree
  node : (ℕ → Tree) → Tree

nodeinj : ∀{f g} → node f ≡ node g → f ≡ g
nodeinj refl = refl

data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree

nodeinjl : ∀{x y x' y'} → BinTree.node x y ≡ node x' y' → x ≡ x'
nodeinjl eq = cong (λ where leaf → leaf
                            (node e e₁) → e) eq

nodeinjr : ∀{x y x' y'} → BinTree.node x y ≡ node x' y' → y ≡ y'
nodeinjr = cong λ where leaf → leaf
                        (node e e₁) → e₁

∷inj1 : {A : Set}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
∷inj1 refl = refl

∷inj2 : {A : Set}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
∷inj2 eq = cong (λ {[] → []
                  ; (_ ∷ e) → e}) eq

-- prove all of the above without pattern matching on equalities!

---------------------------------------------------------
-- konstruktorok diszjunktsaga
------------------------------------------------------

true≠false : true ≢ false
true≠false x = subst (λ {false → ⊥
                       ; true → ⊤}) x tt

-- prove this without pattern matching in this function on e! (use subst!)
true≠false' : true ≢ false
true≠false' ()

zero≠sucn : {n : ℕ} → zero ≢ ℕ.suc n
zero≠sucn eq = subst (λ where zero → ⊤
                              (suc _) → ⊥) eq tt

n≠sucn : (n : ℕ) → n ≢ suc n
n≠sucn zero ()
n≠sucn (suc m) eq = let rec = n≠sucn m (sucinj m (suc m) eq) in rec

-- prove this using induction on n!
n≠sucn' : (n : ℕ) → n ≢ suc n
n≠sucn' n ()

leaf≠node : ∀{f} → Tree.leaf ≢ node f
leaf≠node ()

leaf≠node' : ∀{x y} → BinTree.leaf ≢ node x y
leaf≠node' eq =
  subst 
  (λ where leaf → ℕ
           (node e e₁) → ⊥) eq 0

nil≠cons : {A : Set}{x : A}{xs : List A} → [] ≢ x ∷ xs
nil≠cons eq = subst 
  (λ where [] → Fin 8
           (x ∷ e) → ⊥) eq (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc  fzero)))))))

---------------------------------------------------------
-- egyenlosegek eldonthetosege
------------------------------------------------------

_≟Bool_ : (b b' : Bool) → Dec (b ≡ b')
false ≟Bool false = inl refl
false ≟Bool true = inr (λ ())
true ≟Bool false = inr (λ ())
true ≟Bool true = inl refl

_≟ℕ_ : (n n' : ℕ) → Dec (n ≡ n')
zero ≟ℕ zero = inl refl
zero ≟ℕ suc _ = inr (λ ())
suc n ≟ℕ zero = inr λ ()
suc n ≟ℕ suc n' with n ≟ℕ n'
... | inl a = inl (cong suc a)
... | inr b = inr (λ x → b (sucinj n n' x))

-- is equality for Tree decidable?

_≟BinTree_ : (t t' : BinTree) → Dec (t ≡ t')
leaf ≟BinTree leaf = inl refl
leaf ≟BinTree node t' t'' = inr (λ ())
node t t₁ ≟BinTree leaf = inr (λ ())
node t t₁ ≟BinTree node t' t'' with t ≟BinTree t' | t₁ ≟BinTree t''
... | inl a | inl a₁ = inl (cong₂ node a a₁)
... | inl a | inr b = inr (λ x → b {!   !})
... | inr b | _ = inr (λ x → b {!   !})

_≟List_ : {A : Set} → ({x y : A} → Dec (x ≡ y)) → {xs ys : List A} → Dec (xs ≡ ys)
_≟List_ = {!!}
 