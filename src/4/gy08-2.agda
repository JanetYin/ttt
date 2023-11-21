open import Lib

-- ha igényelt, ezeket még meg lehet nézni közösen, de átugorható
f1 : {X Y : Set} → ¬ ¬ X ⊎ ¬ ¬ Y → ¬ ¬ (X ⊎ Y)
f1 = {!!}

f2 : ({X Y : Set} → ¬ (X × Y) → ¬ X ⊎ ¬ Y) → {X Y : Set} → ¬ ¬ (X ⊎ Y) → ¬ ¬ X ⊎ ¬ ¬ Y
f2 = {!!}

module People
  (Person    : Set) -- univerzum
  (Ann       : Person) -- konstans
  (Kate      : Person) -- konstans
  (Peter     : Person) -- konstans
  (_childOf_ : Person → Person → Set)
  (_sameAs_  : Person → Person → Set) -- ez most itt az emberek egyenlosege
  where

  -- Define the _hasChild predicate.
  _hasChild : Person → Set
  x hasChild = Σ Person λ c → c childOf x

  -- Formalise: Ann is not a child of Kate.
  ANK : Set
  ANK = ¬ (Ann childOf Kate)

  -- Formalise: there is someone with exactly one child.
  ONE : Set
  ONE = Σ Person λ p → Σ Person λ c → c childOf p × (∀(x : Person) → ¬ (x sameAs c) → ¬ (x childOf p))

  -- Define the relation _parentOf_.
  _parentOf_ : Person → Person → Set
  x parentOf y = y childOf x

  -- Formalise: No one is the parent of everyone.
  NOPE : Set
  NOPE = ¬ Σ Person λ p → ∀(p2 : Person) → p parentOf p2

  -- Formalise: No one is the parent of everyone.
  NOPE' : Set
  NOPE' = ∀(p : Person) → ¬ (∀(p2 : Person) → p parentOf p2)

  -- Prove that if Ann has no children then Kate is not the child of Ann.
  AK : ¬ (Σ Person λ y → y childOf Ann) → ¬ (Kate childOf Ann)
  AK = {!!}

  -- Prove that if there is no person who is his own parent than no one is the parent of everyone.
  ¬NOPE : ¬ (Σ Person λ x → x parentOf x) → NOPE
  ¬NOPE = {!!}

-- egy másik formalizálás, ha igényelt még a közös gyakorlás
module Safari
  -- univerzumbeli elemek típusa
  (Animal : Set) -- állat
  -- univerzumbeli elemek
  (Gazella : Animal) -- gazella
  (Giraffe   : Animal) -- zsiráf
  (Zebra  : Animal) -- zebra
  (Lion    : Animal) -- oroszlán
  (Hyena   : Animal) -- hiéna
  -- predikátumok
  (isInMatingSeason : Animal → Set) -- isInMatingSeason X ≡ X párzási időszakában van
  (_mates_ : Animal → Animal → Set) -- X mates Y ≡ Y párja X-nek
  (_same_ : Animal → Animal → Set) -- Két állat ugyanaz.
  where

    -- Formalizáljuk az alábbi kifejezéseket

    -- Minden állat esetén,
    -- ha az az állat éppen nincsen párzási időszakában,
    -- akkor létezik egy másik állat, aki a párja.
    ∃mate : Set
    ∃mate = ∀ a → (isInMatingSeason a → Σ Animal (λ b → ¬ (a same b) × a mates b))

    -- A zebrának nincsen párja.
    noMate4Zebras : Set
    noMate4Zebras = ¬ (Σ Animal λ a → Zebra mates a)

    -- Bizonyítsd be az alábbi kifejezést!
    -- Amennyiben minden állat esetén, ha az az állat nincsen párzási időszakában,
    -- akkor létezik egy másik állat, aki a párja (∃mate),
    -- és a Zebra éppen nincsen párzási időszakában,
    -- akkor nem igaz, hogy a Zebrának nincsen párja (noMate4Zebras).
    lemma : ∃mate × ¬ (isInMatingSeason Zebra) → ¬ noMate4Zebras
    lemma = {!   !}

---------------------------------------------------------
-- predicate (first order) logic laws
---------------------------------------------------------

∀×-distr : (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
∀×-distr A P Q = (λ apq → (λ a → fst (apq a)) , λ a → snd (apq a))
               , λ {(pa , qa) a → pa a , qa a}

∀⊎-distr : (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a) ⊎ ((a : A) → Q a) → ((a : A) → P a ⊎ Q a)
∀⊎-distr A P Q (inl pa) a = inl (pa a)
∀⊎-distr A P Q (inr qa) a = inr (qa a)

∀⊎-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (((a : A) → P a ⊎ Q a) → ((a : A) → P a) ⊎ ((a : A) → Q a)))
∀⊎-distr' = λ f → case (f (Fin 2) P Q λ {zero → inr tt; (suc a) → inl tt}) (λ pa → pa 0) λ qa → qa 1 where
  P : Fin 2 → Set
  P zero = ⊥
  P (suc _) = ⊤

  Q : Fin 2 → Set
  Q zero = ⊤
  Q (suc _) = ⊥

Σ×-distr : (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a × Q a)  → Σ A P × Σ A Q
Σ×-distr = {!!}

Σ×-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (Σ A P × Σ A Q → Σ A λ a → P a × Q a))
Σ×-distr' = λ f → p (f Bool P Q ((true , tt) , false , tt)) where
  P : Bool → Set
  P true = ⊤
  P false = ⊥

  Q : Bool → Set
  Q true = ⊥
  Q false = ⊤

  p : Σ Bool (λ a → P a × Q a) → ⊥
  p (false , x) = fst x
  p (true , x) = snd x

Σ⊎-distr : (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a)  ↔ Σ A P ⊎ Σ A Q
Σ⊎-distr = {!!}

¬∀ : (A : Set)(P : A → Set) → (Σ A λ a → ¬ P a) → ¬ ((a : A) → P a)
¬∀ = {!!}

¬Σ : (A : Set)(P : A → Set) → (¬ Σ A λ a → P a) ↔ ((a : A) → ¬ P a)
¬Σ = {!!}

⊎↔ΣBool : (A B : Set) → (A ⊎ B) ↔ Σ Bool (λ b → if b then A else B)
⊎↔ΣBool = {!!}

¬¬∀-nat : (A : Set)(P : A → Set) → ¬ ¬ ((x : A) → P x) → (x : A) → ¬ ¬ (P x)
¬¬∀-nat = {!!}
 
Σ∀ : (A B : Set)(R : A → B → Set) → (Σ A λ x → (y : B) → R x y) → (y : B) → Σ A λ x → R x y
Σ∀ = {!!}

AC : (A B : Set)(R : A → B → Set) → ((x : A) → Σ B λ y → R x y) → Σ (A → B) λ f → (x : A) → R x (f x)
AC = {!!}
