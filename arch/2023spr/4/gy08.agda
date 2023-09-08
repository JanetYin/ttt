open import lib

---------------------------------------------------------
-- higher order logic
------------------------------------------------------

Dec : ∀{i} → Set i → Set i
Dec A = A ⊎ ¬ A

f4 : Dec ((X Y : Set) → X ⊎ Y → Y)
f4 = inr λ f → f ⊤ ⊥ (inl tt)

f5 : Dec ((X Y Z : Set) → (X → Z) ⊎ (Y → Z) → (X ⊎ Y → Z))
f5 = {!!}

f6 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f6 = {!!}

f7 : Dec ((X Y Z : Set) → (X × Y → Z) → (X → Z) × (Y → Z))
f7 = {!!}

f8 : Dec ((X Y Z : Set) → (X ⊎ Y × Z) → (X ⊎ Y) × (X ⊎ Z))
f8 = {!!}

f9 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → (X ⊎ Y × Z))
f9 = {!!}

f10 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → ((X ⊎ Y) × Z))
f10 = {!!}

---------------------------------------------------------
-- kvantorok
---------------------------------------------------------

{-
P : A → Set egy A elemeire vonatkozó predikátum
ekkor

∀aPa : ∀ a → P a
vagy egyszerűen
∀aPa : (a : A) → P a           -- minden a ∈ A-ra P a-nak van eleme

∃aPa : Σ A P                    -- létezik a ∈ A, amire P a-nak van eleme
-}

∃ : {A : Set} (P : A → Set) → Set
∃ {A} P = Σ A P

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

  ---------------- ezek definíciók

  -- Define the _hasChild predicate.
  _hasChild : Person → Set
  x hasChild =  Σ Person λ t → t childOf x   --létezik Person (nevezzük t-nek), hogy t childOf x

  -- Formalise: Ann is not a child of Kate.
  ANK : Set
  ANK = ¬ (Ann childOf Kate)

  -- Formalise: there is someone with exactly one child.
  ONE : Set
  ONE = Σ Person λ t → Σ Person λ c → c childOf t × ((p : Person) → p childOf t → p sameAs c)

  -- Define the relation _parentOf_.
  _parentOf_ : Person → Person → Set
  x parentOf y = {!!}

  -- Formalise: No one is the parent of everyone.
  NOPE : Set
  NOPE = ¬ Σ Person λ t → ∀ (p : Person) → t parentOf p

  ---------------- ezek már bizonyítások

  -- Prove that if Ann has no children then Kate is not the child of Ann.
  AK : ¬ (Σ Person λ y → y childOf Ann) → ¬ (Kate childOf Ann)
  AK = {!!}

  -- Prove that if there is no person who is his own parent than no one is the parent of everyone.
  irrefl→NOPE : ¬ (Σ Person λ x → x parentOf x) → NOPE
  irrefl→NOPE hyp = λ ope → hyp (fst ope , snd ope (fst ope))

---------------------------------------------------------
-- predicate (first order) logic laws
---------------------------------------------------------

∀×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
fst (∀×-distr A P Q) = λ hyp → (λ a → fst (hyp a)) , λ a → snd (hyp a)
snd (∀×-distr A P Q) = λ hyp → λ a → fst hyp a , snd hyp a
∀⊎-distr-there  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a) ⊎ ((a : A) → Q a) → ((a : A) → P a ⊎ Q a)
∀⊎-distr-there = {!!}
Σ×-distr-there  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a × Q a)  → Σ A P × Σ A Q
Σ×-distr-there A P Q (a , (pa , qa)) = (a , pa) , (a , qa)
Σ⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a)  ↔ Σ A P ⊎ Σ A Q
Σ⊎-distr = {!!}

Σ¬→¬∀        :    (A : Set)(P : A → Set)              → (Σ A λ a → ¬ P a)      → ¬ ((a : A) → P a)
Σ¬→¬∀ = {!!}
-- ez visszafelé nem igaz!
-- miért?

¬Σ↔∀¬        :    (A : Set)(P : A → Set)              → (¬ Σ A λ a → P a)      ↔ ((a : A) → ¬ P a)
¬Σ↔∀¬ = {!!}
⊎↔ΣBool   :    (A B : Set)                         → (A ⊎ B)                ↔ Σ Bool (λ b → if b then A else B)
⊎↔ΣBool = {!!}
¬¬∀-nat   :    (A : Set)(P : A → Set)              → ¬ ¬ ((x : A) → P x)    → (x : A) → ¬ ¬ (P x)
¬¬∀-nat = {!!}

-- itt konkrétan hamisságot bizonyítunk
-- ellenpéldát kell mutatni
∀⊎-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (((a : A) → P a ⊎ Q a) → ((a : A) → P a) ⊎ ((a : A) → Q a)))
∀⊎-distr' f = case helper case₁ {!!}
  where
  helper : ((a : Bool) → a ≡ true) ⊎ ((a : Bool) → a ≡ false)
  helper = f Bool (_≡ true) (_≡ false) (λ { true → inl refl ; false → inr refl} )

  case₁ : ((a : Bool) → a ≡ true) → ⊥
  case₁ f with f false
  case₁ f      | ()

  case₂ : ((a : Bool) → a ≡ false) → ⊥
  case₂ f with f true
  case₂ f      | ()

{-
ez mutatja a logikáját
de ilyet lehetőleg ne csináljatok
≥2 : ℕ → Set
≥2 n with (n - 1)
...    | zero = ⊥
...    | (suc n-1) = ⊤
-}

-- itt is
Σ×-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (Σ A P × Σ A Q → Σ A λ a → P a × Q a))
Σ×-distr' = {!!}

-- ha van kulcs, ami minden ajtót nyit, akkor minden ajtóhoz van kulcs, ami nyitja (de fordítva nem
Σ∀       : (A B : Set)(R : A → B → Set)        → (Σ A λ x → (y : B) → R x y) → (y : B) → Σ A λ x → R x y
Σ∀ = {!!}

-- ha minden kulcshoz van ajtó, amit nyit, akkor létezik egy függvény, ami egy kulcshoz egy hozzá tartozó ajtót ad meg
AC       : (A B : Set)(R : A → B → Set)        → ((x : A) → Σ B λ y → R x y) → Σ (A → B) λ f → (x : A) → R x (f x)
AC = {!!}
