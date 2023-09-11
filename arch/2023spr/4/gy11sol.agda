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
sucinj m n refl = refl

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

-- prove it without pattern matching on e! (hint: use pred)
sucinj' : (m n : ℕ) → suc m ≡ suc n → m ≡ n
sucinj' m n e = cong pred e

-- és ezeket most mind refl-ös mintaillesztés nélkül

data Tree : Set where
  leaf : Tree
  node : (ℕ → Tree) → Tree

nodeinj : ∀{f g} → node f ≡ node g → f ≡ g
nodeinj {t1} {t2} t1≡t2 = cong children t1≡t2
  where
  children : Tree → (ℕ → Tree)
  children (leaf) = λ _ → leaf   -- akármi
  children (node ts) = ts

data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree

nodeinjl : ∀{x y x' y'} → BinTree.node x y ≡ node x' y' → x ≡ x'
nodeinjl e = cong firstChild e
  where
  firstChild : BinTree → BinTree
  firstChild leaf = leaf -- akármi
  firstChild (BinTree.node x _) = x

nodeinjr : ∀{x y x' y'} → BinTree.node x y ≡ node x' y' → y ≡ y'
nodeinjr = {!!}

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

headWithDefault : {A : Set} → A → List A → A 
headWithDefault _   (x ∷ _) = x
headWithDefault def [] = def

∷inj1 : ∀{A}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
∷inj1 {x = x} e = cong (headWithDefault x) e

-- házi
∷inj2 : ∀{A}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
∷inj2 = {!!}

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
n≠sucn' zero e = zero≠sucn {zero} e
n≠sucn' (suc n) e = n≠sucn' n (cong pred e)

leaf≠node : ∀{f} → ¬ (Tree.leaf ≡ node f)
leaf≠node e = subst (λ { Tree.leaf → ⊤ ; (node _) → ⊥ })
                    e
                    tt

leaf≠node' : ∀{x y} → ¬ (BinTree.leaf ≡ node x y)
leaf≠node' = {!!}

nil≠cons : ∀{A}{x : A}{xs} → ¬ ([] ≡ x ∷ xs)
nil≠cons = {!!}

---------------------------------------------------------
-- egyenlosegek eldonthetosege
------------------------------------------------------

-- itt a Dec-et másra hasznlájuk: azt jelenti, hogy mindig ki tudjuk számolni, hogy egyenlő-e
Dec : Set → Set
Dec A = A ⊎ ¬ A

_≟Bool_ : (b b' : Bool) → Dec (b ≡ b')        -- M-x describe-char
false ≟Bool false = inl refl
false ≟Bool true = inr λ e → subst (λ { false → ⊤ ; true → ⊥ }) e tt
true ≟Bool false = inr true≠false
true ≟Bool true = inl refl

_≟ℕ_ : (n n' : ℕ) → Dec (n ≡ n')
zero ≟ℕ zero = inl refl
zero ≟ℕ suc n' = inr {!!}
suc n ≟ℕ zero = inr {!!}
suc n ≟ℕ suc n' = case (n ≟ℕ n') (λ e → inl (cong suc e))
                                  λ f → inr λ se → f (cong pred se)

-- ez trükkös
_≟Tree_ : (t t' : Tree) → Dec (t ≡ t')
_≟Tree_ = {!!}

_≟BinTree_ : (t t' : BinTree) → Dec (t ≡ t')
leaf ≟BinTree leaf = inl refl
leaf ≟BinTree node t' t'' = inr {!!}
node t t₁ ≟BinTree leaf = inr {!!}
node t t₁ ≟BinTree node t' t₁' = case (t ≟BinTree t') (case (t₁ ≟BinTree t₁') (λ e2 e1 → inl
                                                                                         (trans (cong (BinTree.node t) e2) (cong (λ x → BinTree.node x t₁') e1))) {!!}) {!!}

_≟List_ : {A : Set} → ({x y : A} → Dec (x ≡ y)) → {xs ys : List A} → Dec (xs ≡ ys)
_≟List_ = {!!}


---------------------------------------------------------
-- típusokra egyenlőtlenség bizonyítása
------------------------------------------------------

ℕ≠Bool : ¬ (ℕ ≡ Bool)
ℕ≠Bool e = helper (subst (λ A → ¬ hasThreeDistinct A) (sym e) helper2)
  where

  hasThreeDistinct : Set → Set
  hasThreeDistinct A = Σ A λ x → Σ A λ y → Σ A λ z →
                                   ¬ (x ≡ y) × ¬ (x ≡ z) × ¬ (y ≡ z)

  helper : ¬ hasThreeDistinct ℕ → ⊥
  helper f = f (zero , (suc zero) , (suc (suc zero)) ,
                    (λ { () }) , (λ { () }) , λ { () })

  helper2 : ¬ hasThreeDistinct Bool
  helper2 (false , false , b3 , ne1 , ne2 , ne3) = ne1 refl
  helper2 (false , true , false , ne1 , ne2 , ne3) = ne2 refl
  helper2 (false , true , true , ne1 , ne2 , ne3) = ne3 refl
  helper2 (true , false , false , ne1 , ne2 , ne3) = ne3 refl
  helper2 (true , false , true , ne1 , ne2 , ne3) = ne2 refl
  helper2 (true , true , b3 , ne1 , ne2 , ne3) = ne1 refl
