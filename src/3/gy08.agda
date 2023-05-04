open import lib

---------------------------------------------------------
-- higher order logic
------------------------------------------------------

-- ∀f. ≡ ∀ f → ≡ (f : vmi típus) →
-- ∃f. ≡ Σ vmi típus λ f →
-- A v B = A ⊎ B
-- A ∧ B = A × B
-- A ⊃ B = A → B
-- A ⟺ B = A ↔ B
-- ¬ A ≡ A → ⊥

d1 : {A : Set} → (A → A)
d1 = λ x → x

d2 : {A B : Set} → (A ⊎ (B × A)) → A
d2 (inl x) = x
d2 (inr (fst₁ , snd₁)) = snd₁

-- exfalso : ⊥ → A
-- ¬ A ≡ A → ⊥
d3 : {A : Set} → A → ¬ ¬ A
d3 x y = y x

d4 : {A : Set} → ¬ ¬ (¬ ¬ A → A)
d4 x = x (λ x₁ → exfalso (x₁ (λ x₂ → x (λ _ → x₂))))


dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b f = f (λ ¬x×y → inr (λ y → f (λ _ → inl (λ x → ¬x×y (x , y)))))

Dec : ∀{i} → Set i → Set i
Dec A = A ⊎ ¬ A

f : {X Y : Set} → Dec ((¬ (Y → X) → ¬ (X → Y)) → ¬ ¬ ((X → Y) → Y → X))
f = inl (λ x x₁ → x (λ x₂ → x₁ (λ x₃ x₄ → x₂ x₄)) (λ x₂ → exfalso (x₁ (λ _ _ → x₂))))

f4 : Dec ((X Y : Set) → X ⊎ Y → Y)
f4 = inr λ x → x ⊤ ⊥ (inl tt)

f5 : Dec ((X Y Z : Set) → (X → Z) ⊎ (Y → Z) → (X ⊎ Y → Z))
f5 = inr λ x → x ⊥ ⊤ ⊥ (inl λ z → z) (inr tt)

f6 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f6 = inl (λ X Y Z xz×yz x×y → fst xz×yz (fst x×y))

f7 : Dec ((X Y Z : Set) → (X × Y → Z) → (X → Z) × (Y → Z))
f7 = inr (λ x → fst (x ⊤ ⊥ ⊥ snd) tt)

f8 : Dec ((X Y Z : Set) → (X ⊎ Y × Z) → (X ⊎ Y) × (X ⊎ Z))
f8 = inl (λ {
  X Y Z (inl x) → (inl x) , (inl x) ;
  X Y Z (inr x) → (inr (fst x)) , (inr (snd x))})

f9 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → (X ⊎ Y × Z))
f9 = {!!}

f10 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → ((X ⊎ Y) × Z))
f10 = {!!}

---------------------------------------------------------
-- predicate (first order) logic example
---------------------------------------------------------

module People
  (Person    : Set)
  (Ann       : Person)
  (Kate      : Person)
  (Peter     : Person)
  (_childOf_ : Person → Person → Set)
  (_sameAs_  : Person → Person → Set) -- ez most itt az emberek egyenlosege
  where

  -- \GS
  -- \Sigma
  -- Define the _hasChild predicate.
  _hasChild : Person → Set
  x hasChild = Σ Person λ p → p childOf x -- ∃ p. p childOf x

  -- Formalise: Ann is not a child of Kate.
  ANK : Set
  ANK = ¬ (Ann childOf Kate)

  -- \neg
  -- \times
  -- \all
  -- ∃ parent. ∃ child. child isChildOf parent ∧ ∀ child2. (child2 isChildOf parent) ⊃ (child2 sameAs child)
  -- Formalise: there is someone with exactly one child.
  ONE : Set
  ONE = Σ Person
    (λ parent → Σ Person
    λ child → (child childOf parent) ×
    ((child2 : Person) → (child2 childOf parent) → child2 sameAs child))

  -- Define the relation _parentOf_.
  _parentOf_ : Person → Person → Set
  x parentOf y = y childOf x

  -- Formalise: No one is the parent of everyone.
  NOPE : Set
  NOPE = ¬ Σ Person λ parent → ∀ child → parent parentOf child

  -- Prove that if Ann has no children then Kate is not the child of Ann.
  AK : ¬ (Σ Person λ y → y childOf Ann) → ¬ (Kate childOf Ann)
  AK ¬ΣAnn kcoa = ¬ΣAnn (Kate , kcoa)

  -- Prove that if there is no person who is his own parent than no one is the parent of everyone.
  ¬NOPE : ¬ (Σ Person λ x → x parentOf x) → NOPE
  ¬NOPE ¬Σ (p , proof) = ¬Σ (p , proof p)


module Food
  (Food : Set) -- Univerzum
  (apple : Food) -- univ beli elem
  (banana : Food) -- univ beli elem
  (spaghetti : Food) -- univ beli elem
  (isTasty : Food → Set) -- predikátum
  (isDisgusting : Food → Set) -- predikátum
  (_isGoodWith_ : Food → Food → Set) -- predikátum
  (_sameAs_ : Food → Food → Set) -- predikátum
  (notDisgusting : ∀ x → isTasty x ↔ ¬ isDisgusting x) -- axióma
  (notTasty : ∀ x → isDisgusting x ↔ ¬ isTasty x)
  (bananaTasty : isTasty banana)
  where

  -- ∀a ≡ (a : Típus) →
  -- ∀a ≡ ∀ a →
  --
  -- ∃a ≡ Σ A λ a →

  -- a banán finom
  tastyBanana : Set
  tastyBanana = isTasty banana

  -- semmi sem finom
  -- ∀f. ¬ isTasty f
  -- ¬ (∃f. isTasty f)
  ssf : Set
  ssf = (a : Food) → ¬ (isTasty a) -- ∀ a → ¬ isTasty a

  ssf' : Set
  ssf' = ¬ (Σ Food λ a → isTasty a)

  -- ha semmi sem finom, akkor a banán nem finom
  bnt : Set
  bnt = ssf → ¬ tastyBanana

--- ¬ A ≡ A → ⊥
--- ((a : Food) → (isTasty a) → ⊥)
--- tastyBanana


  -- ∧ ≡ ×
  -- v ≡ ⊎
  -- record Σ (A : Set)(B : A → Set) : Set where
    -- constructor _,_
    -- field
      -- fst : A
      -- snd : B fst
  --

  iteΣ : Σ Bool λ b → if b then ℕ else ⊤
  iteΣ = false , tt

  pbnt : bnt
  pbnt ssf tastyBanana = ssf banana tastyBanana

  -- nem létezik undorító és finom étel
  -- ¬ (∃ f. isDisg f ∧ isTasty f) ≡ (∃ f. isDisg f ∧ isTasty f) → ⊥
  ntd : Set
  ntd = ¬ Σ Food λ f → isTasty f × isDisgusting f

  pntd : ntd
  pntd (food , tastyf×disgf) = helper food (snd tastyf×disgf) (fst tastyf×disgf)
    where
      helper : ∀ x → isDisgusting x → ¬ (isTasty x)
      helper = λ x → fst (notTasty x)


  -- minden étel jó valami étellel
  -- ∀f. ∃g. f isGoodWith g
  -- isGoodWith
  egws : Set
  egws = ∀ f → Σ Food λ g → f isGoodWith g

  -- minden finom étel jó saját magával
  -- ∀f. isTasty f → f isGoodWith f
  agwt : Set
  agwt = ∀ f → isTasty f → f isGoodWith f

  -- az unfordító ételek jók minden finom étellel
  -- ∀ f. isDisgusting f → (∀ g. isTasty g → f isGoodWith g)
  ntgwt : Set
  ntgwt = ∀ f → isDisgusting f → ∀ g → isTasty g → f isGoodWith g

  -- minden étel finom vagy undorító
  aton : Set
  aton = ∀ f → isTasty f ⊎ isDisgusting f

  -- Ha aton, ntgwt, agwt akkor egws

  impl : Set
  impl = aton × ntgwt × agwt → egws

  implp : impl -- Σ Food λ g → f isGoodWith g
  -- x : isTasty f
  -- f : Food
  implp (aton , ntgwt , agwt) f = case (aton f) (λ x → f , (agwt f x)) λ x → banana , (ntgwt f x banana bananaTasty)

  -- van olyan étel ami nem finom semmivel
  ent : Set
  ent = Σ Food λ f → ∀ g → ¬ (f isGoodWith g)


module PluMin
  -- univerzumbeli elemek típusa
  (TransitLine : Set) -- járat
  -- univerzumbeli elemek
  (MetrolineM3 : TransitLine) -- M3-as metró
  (Tramline1   : TransitLine) -- 1-es villamos
  (BuslineM30  : TransitLine) -- M30-as busz
  (Busline9    : TransitLine) -- 9-es busz
  (Tramline4   : TransitLine) -- 4-es villamos
  -- predikátumok
  (isAvailable : TransitLine → Set) -- isAvailable X ≡ X közlekedik
  (_replaces_ : TransitLine → TransitLine → Set) -- X replaces Y ≡ Y helyett X közlekedik
  where

    -- Formalizáljuk az alábbi kifejezéseket

    -- Minden járat esetén,
    -- ha az a járat nem közlekedik akkor létezik egy másik járat,
    -- ami helyette közlekedik
    ∃replacement : Set
    ∃replacement = (x : TransitLine) → ¬ (isAvailable x) → Σ TransitLine λ p → p replaces x

    -- Nem közlekedik semmi a 9-es busz helyett
    noreplacementfor9 : Set
    noreplacementfor9 = ∀ x → ¬ (x replaces Busline9)

    -- Bizonyítsd be az alábbi kifejezést!
    -- Ha (∃replacement) minden járat esetén, ha az a járat nem jár, akkor létezik egy másik járat, ami helyette jár,
    -- és a 9-es nem közlekedik, akkor nem igaz, hogy (noreplacementfor9) nem közlekedik semmi a 9-es busz helyett
    lemma : ∃replacement × ¬ (isAvailable Busline9) → ¬ noreplacementfor9
    lemma (fst₁ , snd₁) x₁ = x₁ (fst (fst₁ Busline9 snd₁)) (snd (fst₁ Busline9 snd₁))


---------------------------------------------------------
-- predicate (first order) logic laws
---------------------------------------------------------

∀×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
∀×-distr = {!!}
∀⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a) ⊎ ((a : A) → Q a) → ((a : A) → P a ⊎ Q a)
∀⊎-distr = {!!}
Σ×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a × Q a)  → Σ A P × Σ A Q
Σ×-distr = {!!}
Σ⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a)  ↔ Σ A P ⊎ Σ A Q
Σ⊎-distr = {!!}
¬∀        :    (A : Set)(P : A → Set)              → (Σ A λ a → ¬ P a)      → ¬ ((a : A) → P a)
¬∀ = {!!}
¬Σ        :    (A : Set)(P : A → Set)              → (¬ Σ A λ a → P a)      ↔ ((a : A) → ¬ P a)
¬Σ = {!!}
⊎↔ΣBool   :    (A B : Set)                         → (A ⊎ B)                ↔ Σ Bool (λ b → if b then A else B)
⊎↔ΣBool = {!!}
¬¬∀-nat   :    (A : Set)(P : A → Set)              → ¬ ¬ ((x : A) → P x)    → (x : A) → ¬ ¬ (P x)
¬¬∀-nat = {!!}

∀⊎-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (((a : A) → P a ⊎ Q a) → ((a : A) → P a) ⊎ ((a : A) → Q a)))
∀⊎-distr' = {!!}

Σ×-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (Σ A P × Σ A Q → Σ A λ a → P a × Q a))
Σ×-distr' w = handle absurd
  where
  P' : Bool → Set
  P' true = ⊤
  P' false = ⊥
  Q' : Bool → Set
  Q' true = ⊥
  Q' false = ⊤
  absurd : (Σ Bool λ a → P' a × Q' a)
  absurd = w Bool P' Q' ((true , tt) , (false , tt))
  handle : ¬ (Σ Bool λ a → P' a × Q' a)
  handle (false , snd₁) = fst snd₁
  handle (true , snd₁) = snd snd₁

Σ×-distr'' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (Σ A P × Σ A Q → Σ A λ a → P a × Q a))
Σ×-distr'' w with  (w Bool (λ { true → ⊥ ; false → ⊤ }) (λ { false → ⊥ ; true → ⊤ }) ((false , tt) , true , tt))
... | false , snd₁ = snd snd₁
... | true , snd₁ = fst snd₁

-- with mintaillesztés
f' : ℕ → ℕ
f' x with x + 1
... | zero = 1
... | suc y = 2
 
Σ∀       : (A B : Set)(R : A → B → Set)        → (Σ A λ x → (y : B) → R x y) → (y : B) → Σ A λ x → R x y
Σ∀ = {!!}
AC       :
  (A B : Set)
  (R : A → B → Set) →
  ((x : A) → Σ B λ y → R x y) → Σ (A → B) λ f → (x : A) → R x (f x)
fst (AC A B R f) = λ a → fst (f a)
snd (AC A B R f) = λ a → snd (f a)
