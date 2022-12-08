{- BEGIN FIX -}
module exampleExam where

open import lib

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

-- Fill in the holes!

-- marks:
-- 0-4  1
-- 5-6  2
-- 7-8  3
-- 9-9  4
-- >9   5

{- BEGIN FIX -}
eq3 : ℕ → ℕ → ℕ → Bool
{- END FIX -}
eq3 = {!!}
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
is666 = {!!}
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
weirdLogicalEquiv = {!!}

-- n1 and n2 should be such that n1 ℕ zero suc ≠ n2 ℕ zero suc
{- BEGIN FIX -}
n1 n2 : (A : Set) → A → (A → A) → A
{- END FIX -}
n1 = {!!}
n2 = {!!}
{- BEGIN FIX -}
test-n1-n2 : ¬ (n1 ℕ zero suc ≡ n2 ℕ zero suc)
test-n1-n2 ()
{- END FIX -}

{- BEGIN FIX -}
some¬ : (A : Set) → ¬ ¬ ¬ ¬ A → ¬ ¬ (A ⊎ ⊥)
{- END FIX -}
some¬ = {!!}

{- BEGIN FIX -}
iso : (A B C : Set) → (A ⊎ B → C) ↔ ((A → C) × (B → C))
{- END FIX -}
iso = {!!}

{- BEGIN FIX -}
getX : (X : Set) → X ⊎ X ⊎ (⊤ → X) ⊎ (((A : Set) → A → A) → X) → X
{- END FIX -}
getX = {!!}

{- BEGIN FIX -}
lemma1 : ¬ ((n : ℕ) → 3 + n ≡ n + 1)
{- END FIX -}
lemma1 f = {!!}

{- BEGIN FIX -}
lemma2 : (n : ℕ) → ¬ (3 + n ≡ n + 1)
{- END FIX -}
lemma2 = {!!}

{- BEGIN FIX -}
eq : (x y z : ℕ) → x + (y + y) ≡ (y + 0) + (y + x)
{- END FIX -}
eq = {!!}
