module t5.gy08 where
open import lib hiding (_×_; fst; snd; _,_)

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

-- (n : ℕ) → Vec A n  is the type of dependent functions from (n : ℕ) to Vec a n.
replicate : {A : Type} → A → (n : ℕ) → Vec A n
replicate x zero    = []
replicate x (suc n) = x ∷ replicate x n

-- head and tail are total functions on  Vec A (suc n)

head : {A : Type}{n : ℕ} → Vec A (suc n) → A
head = {!!}

tail : {A : Type}{n : ℕ} → Vec A (suc n) → Vec A n
tail = {!!}

countDownFrom : (n : ℕ) → Vec ℕ n
countDownFrom = {!!}

test-countDownFrom : countDownFrom 3 ≡ 3 ∷ 2 ∷ 1 ∷ []
test-countDownFrom = refl

---------------------------------------------------------
-- Fin n : the finite type with n elements
---------------------------------------------------------

data Fin : ℕ → Type where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

f0 : Fin 0 → ⊥
f0 ()

f1-0 : Fin 1
f1-0 = {!!}

f2-0 f2-1 : Fin 2
f2-0 = {!!}
f2-1 = {!!}

f3-0 f3-1 f3-2 : Fin 3
f3-0 = {!!}
f3-1 = {!!}
f3-2 = {!!}

f4-0 f4-1 f4-2 f4-3 : Fin 4
f4-0 = {!!}
f4-1 = {!!}
f4-2 = {!!}
f4-3 = {!!}

-- Getting the i-th element of a vector, with i : Fin n, is a total operation:
infix 5 _!!_
_!!_ : {A : Type}{n : ℕ} → Vec A n → Fin n → A
xs !! n = {!!}

test-!! : 3 ∷ 4 ∷ 1 ∷ [] !! (suc (suc zero)) ≡ 1
test-!! = refl

vec-map : {A B : Type}(f : A → B){n : ℕ} → Vec A n → Vec B n
vec-map f as = {!!}

data List (A : Type) : Type where
  []  : List A
  _∷_ : A → List A → List A

length : {A : Type} → List A → ℕ
length = {!!}

vec-from-list : {A : Type}(as : List A) → Vec A (length as)
vec-from-list = {!!}

-- append can be defined on vectors.
-- !!! The definition of append depends on the computation of the definition of _+_
_++_ : {A : Type}{m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
_++_ = {!!}

-- The function tabulate should be an inverse of (_!!_)
-- Hint: use induction / pattern-matching on n.
tabulate : {n : ℕ}{A : Type} → (Fin n → A) → Vec A n
tabulate = {!!}

--------------------------------------------------------------------------------
-- Sigma types: the type of dependent pairs
--------------------------------------------------------------------------------

infixr 5 _,_
record Σ (A : Type)(B : A → Type) : Type where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

-- Product types can be redefined using Σ-types
_×_ : Type → Type → Type
_×_ = λ A B → Σ A (λ _ → B)

-- Filter can be defined as a function that returns the filtered vector along with its length.
filter : {A : Type} {n : ℕ} (f : A → Bool) → Vec A n → Σ ℕ (λ n → Vec A n)
filter = {!!}

test-filter : filter (3 <_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ 2 , 4 ∷ 5 ∷ []
test-filter = refl

-- The sigma type Σ ℕ (λ n → Vec A n) is isomorphic to List A
vec↔list : {A : Type} → Σ ℕ (λ n → Vec A n) ↔ List A
vec↔list = {!!}

-- Σ- and Π- types satisfy some of the same isomorphisms as × and →
Σ-assoc : {A : Type} {B : A → Type} {C : (a : A) (b : B a) → Type}
        → (Σ A λ a → Σ (B a) λ b → C a b) ↔ (Σ (Σ A λ a → B a) λ (a , b) → C a b)
Σ-assoc = {!!}

curry : {A : Type} {B : A → Type} {C : (a : A) (b : B a) → Type}
      → ((p : Σ A B) → C (p .fst) (p .snd)) ↔ ((a : A) → (b : B a) → C a b)
curry = {!!}
