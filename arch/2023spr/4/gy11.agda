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
sucinj _ _ refl = refl

-- prove it without pattern matching on e! (hint: use pred)
pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

sucinj' : (m n : ℕ) → suc m ≡ suc n → m ≡ n
sucinj' m n e = cong pred e

data Tree : Set where
  leaf : Tree
  node : (ℕ → Tree) → Tree

invnode : Tree → (ℕ → Tree)
invnode leaf = λ _ → leaf
invnode (node x) = x

nodeinj : ∀{f g} → node f ≡ node g → f ≡ g
nodeinj {f} {g} e = cong invnode e

data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree

destlnode : BinTree → BinTree
destlnode leaf = leaf
destlnode (node x y) = x

nodeinjl : ∀{x y x' y'} → BinTree.node x y ≡ BinTree.node x' y' → x ≡ x'
nodeinjl e = cong destlnode e

nodeinjr : ∀{x y x' y'} → BinTree.node x y ≡ BinTree.node x' y' → y ≡ y'
nodeinjr = {!!}

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

nonEmpty : {A : Set} → List A → Set
nonEmpty [] = ⊥
nonEmpty (_ ∷ _) = ⊤

head : {A : Set} → (ls : List A) → nonEmpty ls → A
head [] ()
head (x ∷ _) hyp = x

∷inj1 : ∀{A}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
∷inj1 {A}{x}{y}{xs}{ys} e = {!!}
  where
    helper : inr x ≡ inr y
    helper = cong (λ { [] → inl zero ; (x ∷ xs) → inr x }) e

∷inj2 : ∀{A}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
∷inj2 = {!!}

-- prove all of the above without pattern matching on equalities!

---------------------------------------------------------
-- konstruktorok diszjunktsaga
------------------------------------------------------

true≠false : ¬ (true ≡ false)
true≠false ()

-- prove this without pattern matching in this function on e! (use subst!)
true≠false' : ¬ (true ≡ false)
true≠false' e = subst (λ { true → ⊤ ; false → ⊥ })
                      e
                      tt

zero≠sucn : ∀{n} → ¬ (zero ≡ suc n)
zero≠sucn e = subst (λ { zero → ⊤ ; (suc n) → ⊥ })
                    e
                    tt

n≠sucn : ∀ n → ¬ (n ≡ suc n)
n≠sucn n ()

-- prove this using induction on n!
n≠sucn' : ∀ n → ¬ (n ≡ suc n)
n≠sucn' zero e = zero≠sucn e
n≠sucn' (suc n) e = n≠sucn' n (cong pred e)

-- ezek házik; hasonlók
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

_≟Bool_ : (b b' : Bool) → ((b ≡ b') ⊎ ¬ (b ≡ b'))
false ≟Bool false = inl refl
false ≟Bool true = inr λ e → true≠false (sym e)
true ≟Bool false = inr true≠false
true ≟Bool true = inl refl

_≟ℕ_ : (n n' : ℕ) → Dec (n ≡ n')        -- \?=
zero ≟ℕ zero = inl refl
zero ≟ℕ suc n' = inr zero≠sucn
suc n ≟ℕ zero = inr λ e → zero≠sucn (sym e)
suc n ≟ℕ suc n' = case (n ≟ℕ n') (λ e → inl (cong suc e))
                                  λ f → inr λ e → f (cong pred e)

{-
-- ez trükkös
_≟Tree_ : (t t' : Tree) → Dec (t ≡ t')
leaf ≟Tree leaf = inl refl
leaf ≟Tree node x = inr {!!}
node x ≟Tree leaf = inr {!!}
node x ≟Tree node x₁ = {!case (x ≟Tree x₁) ? ?!}
-}

_≟BinTree_ : (t t' : BinTree) → Dec (t ≡ t')
_≟BinTree_ = {!!}

_≟List_ : {A : Set} → ({x y : A} → Dec (x ≡ y)) → {xs ys : List A} → Dec (xs ≡ ys)
_≟List_ = {!!}

---------------------------------------------------------
-- típusokra egyenlőtlenség bizonyítása
------------------------------------------------------

ℕ≠Bool : ¬ (ℕ ≡ Bool)
ℕ≠Bool e = {!!}
