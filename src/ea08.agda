module ea08 where

open import lib
----------
-- Kvíz --
----------

{-
3. kérdés:

fromBool : Bool → Set
fromBool true = ⊤
fromBool false = ⊥

Eqb x y = fromBool (if x then y else (not y))

Eqb true y = fromBool (if true then y else (not y))
Eqb true y = fromBool y
Eqb true true = fromBool true = ⊤
Eqb true false = fromBool false = ⊥

Eqb false y = fromBool (if false then y else (not y))
Eqb false y = fromBool (not y)
Eqb false true = fromBool (not true) = fromBool false = ⊥
Eqb false false = fromBool (not false) = fromBool true = ⊤
4. kérdés:

Az alábbi logikai ekvivalencia mely A,B-re teljesül?
Σ A B ↔ ((x : A) → B x)

A = Bool
B true = ⊤
B false = ⊥

(true , tt) : Σ Bool (λ a → if a then ⊤ else ⊥)
(false, ? : ⊥ típusú érték kéne)

f : (x : Bool) → if x then ⊤ else ⊥
f true = tt
f false = ? : ⊥ típusú érték kéne.

Nem teljesül a logikai ekvivalencia.

A = ⊤
B x = ℕ

Σ ⊤ (λ _ → ℕ) ≅ ⊤ × ℕ    |⊤ × ℕ| = |⊤| × |ℕ| = |ℕ|
(x : ⊤) → ℕ      | ⊤ → ℕ | = |ℕ|^|⊤| = |ℕ|¹ = |ℕ|

Logikai ekvivalencia teljesül.

A = Bool
B x = Bool

Σ Bool (λ _ → Bool) ≅ Bool × Bool   2 × 2 = 4 elemű
(x : Bool) → Bool                   2² = 4
Logikai ekvivalencia teljesül.

A = ⊥
B x = ⊤

Σ ⊥ (λ _ → ⊤) = ⊥ × ⊤    0 elemű
(x : ⊥) → ⊤              1⁰ = 1

A = ℕ
B n = Vec ⊤ n

|Σ ℕ (Vec ⊤)| = |ℕ|
(0 , [])
(1 , tt ∷ [])
(2 , tt ∷ tt ∷ [])

f : (x : ℕ) → Vec ⊤ x
f zero = []
f (suc x) = tt ∷ f x

|(x : ℕ) → Vec ⊤ x| = |ℕ|
-}

∀× : {A : Set}{P : A → Set}{Q : A → Set} →
  ((x : A) → P x × Q x) ↔
  ((x : A) → P x) × ((x : A) → Q x)
∀× = to , from where
  to : {A : Set}{P : A → Set}{Q : A → Set} →
    ((x : A) → P x × Q x) →
    ((x : A) → P x) × ((x : A) → Q x)
  to f = (λ x → fst (f x)) , λ x → snd (f x)

  from : {A : Set}{P : A → Set}{Q : A → Set} →
    ((x : A) → P x) × ((x : A) → Q x) →
    ((x : A) → P x × Q x)
  from (f , g) x = f x , g x

∀⊎1 : ¬ ({A : Set}{P : A → Set}{Q : A → Set} →
  ((x : A) → P x ⊎ Q x) →
  ((x : A) → P x) ⊎ ((x : A) → Q x))
∀⊎1 f = case 
  (f {Bool} {P} {Q} 
    (λ {true → inr tt ; false → inl tt}))
      (λ ∀xPx → ∀xPx true) (λ ∀xQx → ∀xQx false) where
    P : Bool → Set
    P false = ⊤
    P true = ⊥

    Q : Bool → Set
    Q false = ⊥
    Q true = ⊤

∀⊎2 : {A : Set}{P : A → Set}{Q : A → Set} →
  ((x : A) → P x) ⊎ ((x : A) → Q x) →
  ((x : A) → P x ⊎ Q x)
∀⊎2 (inl f) x = inl (f x)
∀⊎2 (inr g) x = inr (g x)

-- ∃∧ : ∃x (P x × Q x) → ∃x (P x) × ∃x (Q x)

------------------------------------------------------------
-- data _≡_ {i}{A : Set i}(a : A) : A → Set i where
--   refl : a ≡ a

trans : ∀{i}{A : Set i}{a b c : A} →
  a ≡ b → b ≡ c → a ≡ c
trans refl b≡c = b≡c

sym : ∀{i}{A : Set i}{a b : A} → a ≡ b → b ≡ a
sym refl = refl

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){a a' : A} →
  a ≡ a' → f a ≡ f a'
cong f refl = refl

{-
uncong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){a a' : A} →
  f a ≡ f a' → a ≡ a'
uncong f fa≡fa' = {! fa≡fa'  !}

f injektív-e.
-}

subst : ∀{i j}{A : Set i}(B : A → Set j) →
  {x y : A} → x ≡ y → B x → B y
subst B refl bx = bx

-- Következő előadás 13 perccel rövidebb.
