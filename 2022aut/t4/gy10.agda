module t4.gy10 where
open import lib hiding (_×_; fst; snd; _,_; _↔_)
open import Agda.Primitive

-- List of unicode symbols:
--    →       \to
--            \rightarrow
--    ℕ       \bN           'b'lackboard 'N', there is also \bZ for ℤ, etc
--    λ       \Gl           'G'reek 'l', there is also \GG for Γ, etc
--            \lambda
--    ×       \times
--    ⊎       \u+
--    ⊤       \top
--    ⊥       \bot
--    ↔       \lr
--    ₁       \_1
--    ₐ       \_a
--    ¹       \^1
--    Σ       \Sigma

---------------------------------------------------------
-- vectors: lists indexed by their length.
---------------------------------------------------------

infixr 6 _∷_
data Vec (A : Type) : ℕ → Type where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

data List (A : Type) : Type where
  []  : List A
  _∷_ : A → List A → List A

length : {A : Type} → List A → ℕ
length [] = 0
length (x ∷ xs) = 1 + length xs

vec-from-list : {A : Type}(as : List A) → Vec A (length as)
vec-from-list [] = []
vec-from-list (x ∷ xs) = x ∷ vec-from-list xs

---------------------------------------------------------
-- Fin n : the finite type with n elements
---------------------------------------------------------

data Fin : ℕ → Type where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

--------------------------------------------------------------------------------
-- Sigma types: the type of dependent pairs
--------------------------------------------------------------------------------

-- (Ignore the universe levels i, j)

infixr 5 _,_
record Σ {i j} (A : Set i)(B : A → Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

-- Product types can be redefined using Σ-types
_×_ : ∀ {i j} → Set i → Set j → Set (i ⊔ j)
_×_ = λ A B → Σ A (λ _ → B)

infix 0 _↔_
_↔_ : ∀{i j} → Set i → Set j → Set (i ⊔ j)
A ↔ B = (A → B) × (B → A)

-- Filter can be defined as a function that returns the filtered vector along with its length.
filter : {A : Type} {n : ℕ} (f : A → Bool) → Vec A n → Σ ℕ (λ n → Vec A n)
filter = {!!}

test-filter : filter (3 <_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ 2 , 4 ∷ 5 ∷ []
test-filter = refl

-- The sigma type Σ ℕ (λ n → Vec A n) is isomorphic to List A
vec→list : {A : Type} → Σ ℕ (λ n → Vec A n) → List A
vec→list = {!!}

list→vec : {A : Type} → List A → Σ ℕ (λ n → Vec A n)
list→vec = {!!}

-- Σ- and Π- types satisfy some of the same isomorphisms as × and →
Σ-assoc : {A : Type} {B : A → Type} {C : (a : A) (b : B a) → Type}
        → (Σ A λ a → Σ (B a) λ b → C a b) ↔ (Σ (Σ A λ a → B a) λ (a , b) → C a b)
Σ-assoc = {!!}

curry : {A : Type} {B : A → Type} {C : (a : A) (b : B a) → Type}
      → ((p : Σ A B) → C (p .fst) (p .snd)) ↔ ((a : A) → (b : B a) → C a b)
curry = {!!}

-- Sigma-types indexed by Bool are binary sum types
-- Non-dependent Sigma-types are binary product types
Σ=⊎ : {A B : Type} → Σ Bool (if_then A else B) ↔ A ⊎ B
Σ=⊎ = {!!}

Σ=× : {A B : Type} → Σ A (λ _ → B) ↔ A × B
Σ=× = {!!}

-- Pi-types indexed by Bool are binary product types
-- Non-dependent Pi-types are function types
→=× : {A B : Type} → ((b : Bool) → if b then A else B) ↔ A × B
→=× = {!!}

Π=→ : {A B : Type} → ((a : A) → (λ _ → B) a) ≡ (A → B)
Π=→ = {!!}

--------------------------------------------------------------------------------
--- Equality types
--------------------------------------------------------------------------------

EqBool : Bool → Bool → Type
EqBool true  true   = ⊤
EqBool false true   = ⊥
EqBool true  false  = ⊥
EqBool false false  = ⊤

-- Alternative:
-- data EqBool' : Bool → Bool → Type where
--   eq-true  : EqBool' true true
--   eq-false : EqBool' false false
-- + general equality types _≡_

-- Reflexivity
refl-Bool : {b : Bool} → EqBool b b
refl-Bool {b} = {!!}

-- Symmetry
sym-Bool : {x y : Bool} → EqBool x y → EqBool y x
sym-Bool {x} {y} = {!!}

-- Transitivity
trans-Bool : {x y z : Bool} → EqBool x y → EqBool y z → EqBool x z
trans-Bool {x} {y} {z} = {!!}

-- Transport: if x = y, then P x is equivalent to P y for any P : Bool → Type
-- Elements of P x can be "transported" to P y
transport-Bool : (P : Bool → Type) → (x y : Bool) → EqBool x y → P x → P y
transport-Bool = {!!}

not = λ b → if b then false else true

not-not : (b : Bool) → EqBool (not (not b)) b
not-not = {!!}

not-injective : (x y : Bool) → EqBool (not x) (not y) → EqBool x y
not-injective = {!!}

-- Boolean equality is decidable
dec-EqBool : (x y : Bool) → EqBool x y ⊎ (¬ EqBool x y)
dec-EqBool = {!!}

-- proof: f is either not, id, const true or const false.
f3 : (f : Bool → Bool) (b : Bool) → EqBool (f (f (f b))) (f b)
f3 f b = {!!}
  where
    f3-helper : (x y : Bool) → EqBool x (f true) → EqBool y (f false) → ∀ b → EqBool (f (f (f b))) (f b)
    f3-helper x y pt pf b = {!!}
