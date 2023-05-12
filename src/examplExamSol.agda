{- BEGIN FIX -}
module exampleExamSol where

open import Agda.Primitive

open import Agda.Builtin.Nat
  renaming (Nat to ℕ)
  public
open import Agda.Primitive
Type = Set
open import Agda.Builtin.Equality
  public
open import Agda.Builtin.Bool
  public
open import Agda.Builtin.Sigma
  public

infixr 2 _×_
infixr 1 _⊎_
infix 0 _↔_

if_then_else_ : ∀{i}{A : Set i}(t : Bool)(u v : A) → A
if true  then u else v = u
if false then u else v = v

-- Product types
_×_ : ∀{ℓ κ} → Set ℓ → Set κ → Set (ℓ ⊔ κ)
A × B = Σ A λ _ → B

-- Sum types
data _⊎_ {i}{j}(A : Set i)(B : Set j) : Set (i ⊔ j) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

case : ∀ {i j k}{A : Set i}{B : Set j}{C : Set k}
         (t : A ⊎ B)(u : A → C)(v : B → C) → C
case (inl t) u v = u t
case (inr t) u v = v t

-- Empty type
data ⊥ : Set where

exfalso : ∀{i}{A : Set i} → ⊥ → A
exfalso ()

-- Unit type
record ⊤ : Set where
  constructor tt
open ⊤ public

_↔_ : ∀{i j} → Set i → Set j → Set (i ⊔ j)
A ↔ B = (A → B) × (B → A)

¬_ : ∀{i} → Set i → Set i
¬ A = A → ⊥

-- defined functions

sym : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

transp : ∀{i j}{A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y
transp P refl p = p

ass+ : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
ass+ zero    b c = refl
ass+ (suc a) b c = cong suc (ass+ a b c)

idr+ : (a : ℕ) → a + 0 ≡ a
idr+ zero    = refl
idr+ (suc a) = cong suc (idr+ a)

+suc : (a b : ℕ) → suc a + b ≡ a + suc b
+suc zero    b = refl
+suc (suc a) b = cong suc (+suc a b)

comm+ : (a b : ℕ) → a + b ≡ b + a
comm+ zero b = sym (idr+ b)
comm+ (suc a) b = trans (cong suc (comm+ a b)) (+suc b a)

_≤_ : ℕ → ℕ → Set
x ≤ y = Σ ℕ λ m → m + x ≡ y

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

infix  3 _∎
infixr 2 _≡⟨_⟩_

_≡⟨_⟩_ : ∀{i}{A : Set i}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

_∎ : ∀{i}{A : Set i}(a : A) → a ≡ a
a ∎ = refl


-- Fill in the holes!

-- marks:
-- 0-4  1
-- 5-6  2
-- 7-8  3
-- 9-9  4
-- >9   5

-- Agda Symbol List: https://people.inf.elte.hu/divip/AgdaTutorial/Symbols.html

{- BEGIN FIX -}
eq3 : ℕ → ℕ → ℕ → Bool
{- END FIX -}
eq3 m n o = eq m n ∧ eq n o
  where
    eq : ℕ → ℕ → Bool
    eq zero zero = true
    eq (suc m) (suc n) = eq m n
    eq _ _ = false
    _∧_ : Bool → Bool → Bool
    true ∧ a = a
    false ∧ _ = false
{- BEGIN FIX -}
test-eq3-1 : eq3 323 323 (321 + 2) ≡ true
test-eq3-1 = refl
test-eq3-2 : eq3 323 323 321 ≡ false
test-eq3-2 = refl
test-eq3-3 : eq3 323 321 323 ≡ false
test-eq3-3 = refl
test-eq3-4 : eq3 321 323 323 ≡ false
test-eq3-4 = refl
test-eq3-5 : eq3 321 323 321 ≡ false
test-eq3-5 = refl
{- END FIX -}

{- BEGIN FIX -}
is666 : ℕ → Bool
{- END FIX -}
is666 = eq 666
  where
    eq : ℕ → ℕ → Bool
    eq zero zero = true
    eq (suc m) (suc n) = eq m n
    eq _ _ = false
{- BEGIN FIX -}
test-is666-1 : is666 666 ≡ true
test-is666-1 = refl
test-is666-2 : is666 667 ≡ false
test-is666-2 = refl
test-is666-3 : is666 665 ≡ false
test-is666-3 = refl
{- END FIX -}

{- BEGIN FIX -}
weirdLogicalEquiv : (A B C : Set) → (A → (B → C × A)) ↔ (B × A → (C ⊎ ⊥))
{- END FIX -}
weirdLogicalEquiv A B C = (λ f ba → inl (fst (f (snd ba) (fst ba)))) , (λ f a b → (case (f (b , a)) (λ c → c) (λ ())) , a)

-- n1 and n2 should be such that n1 ℕ zero suc ≠ n2 ℕ zero suc
{- BEGIN FIX -}
n1 n2 : (A : Set) → A → (A → A) → A
{- END FIX -}
n1 = λ A z s → z
n2 = λ A z s → s z
{- BEGIN FIX -}
test-n1-n2 : ¬ (n1 ℕ zero suc ≡ n2 ℕ zero suc)
test-n1-n2 ()
{- END FIX -}

{- BEGIN FIX -}
some¬ : (A : Set) → ¬ ¬ ¬ ¬ A → ¬ ¬ (A ⊎ ⊥)
{- END FIX -}
some¬ = λ A nnnna nab → nnnna λ nna → nna λ a → nab (inl a)

{- BEGIN FIX -}
iso : (A B C : Set) → (A ⊎ B → C) ↔ ((A → C) × (B → C))
{- END FIX -}
iso A B C = (λ f → (λ a → f (inl a)) , (λ b → f (inr b))) , (λ f ab → case ab (fst f) (snd f))

{- BEGIN FIX -}
getX : (X : Set) → X ⊎ X ⊎ (⊤ → X) ⊎ (((A : Set) → A → A) → X) → X
{- END FIX -}
getX X (inl x) = x
getX X (inr (inl x)) = x
getX X (inr (inr (inl f))) = f tt
getX X (inr (inr (inr g))) = g λ A a → a

{- BEGIN FIX -}
lemma1 : ¬ ((n : ℕ) → 3 + n ≡ n + 1)
{- END FIX -}
lemma1 f = 3≠1 (f 0)
  where
    3≠1 : ¬ (3 ≡ 1)
    3≠1 ()

{- BEGIN FIX -}
lemma2 : (n : ℕ) → ¬ (3 + n ≡ n + 1)
{- END FIX -}
lemma2 (suc n) e = lemma2 n (injsuc e)
  where
    injsuc : {a b : ℕ} → suc a ≡ suc b → a ≡ b
    injsuc refl = refl

{- BEGIN FIX -}
eq : (x y z : ℕ) → x + (y + y) ≡ (y + 0) + (y + x)
{- END FIX -}
eq x y z = trans
  (trans (sym (ass+ x y y))
  (trans (cong (_+ y) (comm+ x y))
  (trans (ass+ y x y)
  (cong (y +_) (comm+ x y)))))
  (sym (cong (_+ (y + x)) (idr+ y)))
