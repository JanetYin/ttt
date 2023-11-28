
{-
(x : ℕ) → P x → Σ ℕ λ y → (Eq x y → ⊥) × Q y
∀ x     . P(x)→ ∃ y     .  x ≠ y       ∧ Q(y)


Bool × Bool   ↔    Bool → Bool

Σ ℕ (Vec ⊤)   ↔    (x : ℕ)→Vec ⊤ n
Vec ⊤ n ≅ ⊤
tt∷tt∷tt∷[] : Vec ⊤ 3
ℕ × ⊤         ↔    ℕ → ⊤

⊤                  ⊤ × ⊥
Bool → A   ≅   A × A
(x:Bool) → if x then A else B   ≅   A × B

(⊥ × ⊤)       (⊥ → ⊤)

⊤ × ℕ         ⊤ → ℕ
-}

open import Lib hiding (cong; sym; trans)

and and' and'' : Bool → Bool → Bool
and true  true  = true
and true  false = false
and false true  = false
and false false = false

and' true  a = a
and' false _ = false

and'' a true  = a
and'' _ false = false

-- unit testek

test1 : and'' true false ≡ false
test1 = refl

-- ...

-- bizonyitsuk be, hogy a true j.o-i egysegeleme az and-nek

-- 0 + a = a , a + 0 = a   <- 0 egysegelem

right-id : (a : Bool) → and a true ≡ a
right-id false = refl
right-id true = refl

right-id' : (a : Bool) → and' a true ≡ a
right-id' false = refl
right-id' true = refl

right-id'' : (a : Bool) → and'' a true ≡ a
right-id'' a = refl

left-id' : (a : Bool) → and' true a ≡ a
left-id' a = refl

+-idl : (n : ℕ) → 0 + n ≡ n
+-idl n = refl

cong : {A B : Set}(f : A → B){a a' : A} → a ≡ a' → f a ≡ f a'
cong f refl = refl

cong-suc : {n m : ℕ} → n ≡ m → suc n ≡ suc m
cong-suc {n} {.n} refl = refl

+-idr : (n : ℕ) → n + 0 ≡ n
-- +-idr zero = refl
-- +-idr (suc n) = cong suc (+-idr n)

-- teljes indukcio
ind : (P : ℕ → Set) →                 -- ite : (A : Set) →    rec : (A : Set) →
  P zero →                            --   A →                  A → 
  ((m : ℕ) → P m → P (suc m)) →       --   (A → A) →            (ℕ → A → A) → 
  (n : ℕ) → P n                       --   ℕ → A                ℕ → A
ind P z s zero    = z
ind P z s (suc n) = s n (ind P z s n)

+-idr = ind (λ n → n + 0 ≡ n) refl (λ m ih → cong suc ih)

-- strukturalis indukcio (minden data-val megadott (induktiv) tipusra), eliminator, fuggo eliminator, elimination principle

data Tree : Set where
  leaf : Tree
  node : Tree → Tree → Tree

-- HF: bebizonyitani, hogy (t : Tree) → leafCount t ≤ 2 ^ (height t)

iteTree : (A : Set) →
  A →
  (A → A → A) →
  Tree → A
iteTree P l n leaf = l
iteTree P l n (node t t') = n (iteTree P l n t) (iteTree P l n t')

indTree : (P : Tree → Set) →
  P leaf →
  ((t t' : Tree) → P t → P t' → P (node t t')) →
  (t : Tree) → P t
indTree P l n leaf = l
indTree P l n (node t t') = n t t' (indTree P l n t) (indTree P l n t')

data Vec (A : Set) : ℕ → Set where
  nil  : Vec A 0
  cons : {n : ℕ} → A → Vec A n → Vec A (suc n)

iteVec : {A : Set}(B : ℕ → Set) →
  B 0 →
  ((n : ℕ) → A → B n → B (suc n)) →
  {n : ℕ} → Vec A n → B n
iteVec B n c nil = n
iteVec B n c (cons a xs) = c _ a (iteVec B n c xs)

-- data _≡_ {A : Set} (a : A) : A → Set
--   refl : a ≡ a

ite≡ : {A : Set}{a : A}(B : A → Set) → B a → {x : A} → a ≡ x → B x
ite≡ B r refl = r

-- subst : {A : Set}(P : A → Set){x y : A} → x ≡ y → P x → P y

sym : {A : Set}{x y : A} → x ≡ y → y ≡ x
-- sym refl = refl
sym {A}{x}{y} e = subst (λ y → y ≡ x) e refl
-- kene egy P, hogy P y = (y ≡ x), P x meg trivialis
-- subst P e : P x         → P y
-- subst P e : (trivialis) → (y ≡ x)

trans : {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl e' = e'

trans' : {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans' e refl = e

trans'' : {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans'' refl refl = refl

-- ite : (A : Set) → A → A → Bool → A
indBool : (P : Bool → Set) →
  P true → P false → (b : Bool) → P b
indBool P t f true  = t
indBool P t f false = f

ind⊎ : {A B : Set}(P : A ⊎ B → Set) →
  ((a : A) → P (inl a)) → ((b : B) → P (inr b)) → (w : A ⊎ B) → P w
ind⊎ P l r (inl a) = l a
ind⊎ P l r (inr b) = r b

-- idl, idr, ass

ass : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
ass a b c = ind (λ a → (a + b) + c ≡ a + (b + c))
  refl
  (λ a e → cong suc e)
  a

-- jovo oran: lesz comm, *-ra vonatkozo egyenlosegek stb.

-- kov. ora 1 perccel rovidebb
