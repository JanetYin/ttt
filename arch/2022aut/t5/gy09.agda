module t5.gy09 where
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
record Σ {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
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


fst' : ∀ {A : Type} {B : A → Type} → Σ A B → A
fst' p = p .fst

snd' : ∀ {A : Type} {B : A → Type} → (p : Σ A B) → B (fst' p)
snd' p = p .snd

pair : ∀ {A : Type} {B : A → Type} (a : A) (b : B a) → Σ A B
pair a b = (a , b)

ΣFin : Type
ΣFin = Σ ℕ λ n → Fin n
-- type whose elements are pairs (n , i)
--  n : ℕ
--  i : Fin n  /  i < n

p0 : ΣFin
p0 = 4 , suc (suc zero) -- 4 , 2

-- p1 : ΣFin
-- p1 = 0 , zero

-- Filter can be defined as a function that returns the filtered vector along with its length.

filter-list : {A : Type} (f : A → Bool) → List A → List A
filter-list f []
  = []
filter-list f (x ∷ xs)
  = if f x then x ∷ filter-list f xs else filter-list f xs

cons-ΣVec : {A : Type} → A → Σ ℕ (λ n → Vec A n) → Σ ℕ (λ n → Vec A n)
cons-ΣVec x (n , xs) = suc n , x ∷ xs
--                     ^ C-c C-s to fill the hole with the unique solution

filter : {A : Type} {n : ℕ} (f : A → Bool) → Vec A n → Σ ℕ (λ n → Vec A n)
filter f []
  = 0 , []
filter f (x ∷ xs)
  = if f x
    then cons-ΣVec x (filter f xs)
    else filter f xs

test-filter : filter (3 <_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ 2 , 4 ∷ 5 ∷ []
test-filter = refl

-- The sigma type Σ ℕ (λ n → Vec A n) is isomorphic to List A
vec→list : {A : Type} → Σ ℕ (λ n → Vec A n) → List A
vec→list (0 , []) = []
vec→list (suc n , x ∷ xs) = x ∷ vec→list (n , xs)

list→vec : {A : Type} → List A → Σ ℕ (λ n → Vec A n)
list→vec [] = 0 , []
list→vec (x ∷ xs) = cons-ΣVec x (list→vec xs)

-- Σ- and Π- types satisfy some of the same isomorphisms as × and →
Σ-assoc : {A : Type} {B : A → Type} {C : (a : A) (b : B a) → Type}
        → (Σ A λ a → Σ (B a) λ b → C a b) ↔ (Σ (Σ A λ a → B a) λ { (a , b) → C a b })
Σ-assoc .fst (a , (b , c)) = (a , b) , c
Σ-assoc .snd ((a , b) , c) = a , (b , c)

curry : {A : Type} {B : A → Type} {C : (a : A) (b : B a) → Type}
      → ((p : Σ A B) → C (p .fst) (p .snd)) ↔ ((a : A) → (b : B a) → C a b)
curry .fst f a b = f (a , b)
curry .snd f (a , b) = f a b

-- Sigma-types indexed by Bool are binary sum types
-- Non-dependent Sigma-types are binary product types
Σ=⊎ : {A B : Type} → Σ Bool (if_then A else B) ↔ A ⊎ B
Σ=⊎ .fst (true , x) = inl x
Σ=⊎ .fst (false , x) = inr x
Σ=⊎ .snd (inl x) = true , x
Σ=⊎ .snd (inr x) = false , x

Σ=× : {A B : Type} → Σ A (λ _ → B) ↔ A × B
Σ=× .fst x = x
Σ=× .snd x = x

-- Pi-types indexed by Bool are binary product types
-- Non-dependent Pi-types are function types
→=× : {A B : Type} → ((b : Bool) → if b then A else B) ↔ A × B
→=× .fst f = f true , f false
→=× .snd (a , b) true = a
→=× .snd (a , b) false = b

Π=→ : {A B : Type} → ((a : A) → (λ _ → B) a) ≡ (A → B)
Π=→ = refl

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
refl-Bool {false} = tt
refl-Bool {true} = tt

-- Symmetry
sym-Bool : {x y : Bool} → EqBool x y → EqBool y x
sym-Bool {false} {false} = λ _ → tt
sym-Bool {false} {true} = λ z → z
sym-Bool {true} {false} = λ z → z
sym-Bool {true} {true} = λ _ → tt

-- Transport: if x = y, then P x is equivalent to P y for any P : Bool → Type
-- Elements of P x can be "transported" to P y
transport-Bool : (P : Bool → Type) → (x y : Bool) → EqBool x y → P x → P y
transport-Bool P false false _ d = d
transport-Bool P true true _ d = d

-- Transitivity
trans-Bool : {x y z : Bool} → EqBool x y → EqBool y z → EqBool x z
trans-Bool {x} {y} {z} p q = transport-Bool (λ z → EqBool x z) _ _ q p


not = λ b → if b then false else true

not-not : (b : Bool) → EqBool (not (not b)) b
not-not false = tt
not-not true = tt

not-injective : (x y : Bool) → EqBool (not x) (not y) → EqBool x y
not-injective false false = λ _ → tt
not-injective false true = λ z → z
not-injective true false = λ z → z
not-injective true true = λ _ → tt

-- Boolean equality is decidable
dec-EqBool : (x y : Bool) → EqBool x y ⊎ (¬ EqBool x y)
dec-EqBool false false = inl tt
dec-EqBool false true = inr (λ x → x)
dec-EqBool true false = inr (λ x → x)
dec-EqBool true true = inl tt

-- Every function Bool → Bool is a congruence
cong-Bool : ∀ {x y} → (f : Bool → Bool) → EqBool x y → EqBool (f x) (f y)
cong-Bool {x} f p = transport-Bool (λ y → EqBool (f x) (f y)) x _ p refl-Bool


-- harder bonus exercise:
-- proof: f is either not, id, const true or const false.
-- hint: use the pigeonhole principle for Bool:
--  pigeonhole : ∀ {x y z : Bool} → EqBool x y ⊎ EqBool y z ⊎ EqBool x z
--
-- f3 : (f : Bool → Bool) (b : Bool) → EqBool (f (f (f b))) (f b)
-- f3 f b = {!!}
