module lec09 where

module example where
  data _≡_ {A : Set}(a : A) : A → Set where
    refl : a ≡ a

open import Lib

data VecWith {A : Set}(a : A) : ℕ → Set where
  one  : VecWith a 0
  cons : A → {n : ℕ} → VecWith a n → VecWith a (suc n)

getTheEl : {A : Set}{a : A}{n : ℕ} → VecWith a n → A
getTheEl {_}{a} _ = a

_++_ : {A : Set}{a : A}{m n : ℕ} → VecWith a m → VecWith a n → VecWith a (m + n)
one ++ ys = ys
cons x xs ++ ys = cons x (xs ++ ys)

-- (.) :: forall a b c . (b -> c) -> (a -> b) -> a -> c
-- _∘_ : {A B C : Set} → (B → C) → (A → B) → A → C  -- (f ∘ g) ∘ h

-- Russell's paradox: Weird X := X ∈ X,  A := {X | ¬ Weird X} = {X | X ∉ X}   A∈A
-- solutions in set theory: ZF (Zermelo-Fraenkel), Neumann (NBG Neumann Bernays Gödel)
-- Haskell: [ x | x <-[1..], isEven x]
-- Per Martin-Löf's first type theory had Set : Set
-- in Haskell, * :: *
-- Girard showed that Set : Set is inconsistent (Girard's paradox)
-- but we also have Russell's paradox in type theory (it uses inductive types (data))

anEquality : 3 ≡ 3
anEquality = refl {lzero}{ℕ}{3}

anEquality' : ℕ ≡ ℕ
anEquality' = refl {lsuc lzero}{Set}{ℕ}

_&&_ : Bool → Bool → Bool
true && a = a
false && _ = false

aUnitTest : true && false ≡ false
aUnitTest = refl

aProof : (a : Bool) → true && a ≡ a -- true is a left identity
aProof a = refl

rightId : (a : Bool) → a && true ≡ a
rightId false = refl
rightId true = refl

-- definitional equality     equality type (propositional equality)
---------------------------------------------------------------------
-- computation               needs a proof
-- the computer can do it
-- can be proven by refl     we might need to do lots of work
-- we cannot talk about it   we can talk about it in type theory

congsuc : (a b : ℕ) → a ≡ b → suc a ≡ suc b
congsuc a .a refl = refl {lzero}{ℕ}{suc a}
--           ^  refl {lzero}{ℕ}{suc a}

cong' : {A B : Set}(f : A → B){a a' : A} → a ≡ a' → f a ≡ f a'
cong' f refl = refl


idl : (n : ℕ) → 0 + n ≡ n
idl n = refl
-- zero  + m = m
-- suc n + m = suc (n + m)
idr : (n : ℕ) → n + 0 ≡ n
idr zero = refl
idr (suc n) = cong suc(idr n)

-- principle of induction on ℕ (teljes indukcio elve, dependent elimination principle, dependent eliminator):
-- to prove that a predicate P holds for all natural numbers:   (P is called motive)
-- 1. P zero                        -- these are called methods
-- 2. ∀ n → P n → P (suc n)         --    P n is the induction hypothesis
-----------------------------
-- (n : ℕ) → P n                    -- n is called target

-- "induction is adequatly typed iteration/recursion"

-- iteℕ :              A      → (          A   → A)         → ℕ       → A
-- recℕ :              A      → (ℕ       → A   → A)         → ℕ       → A
indℕ : (P : ℕ → Set) → P zero → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
indℕ P z s zero = z
indℕ P z s (suc n) = s n (indℕ P z s n)

iteℕ : {A : Set} → A      → (A → A)         → ℕ       → A
iteℕ {A} z s = indℕ (λ _ → A) z (λ _ → s)
recℕ : {A : Set} → A      → (ℕ → A → A)         → ℕ       → A
recℕ {A} = indℕ (λ _ → A)

idr' : (n : ℕ) → n + 0 ≡ n
idr' n = indℕ
  (λ n → n + 0 ≡ n)
  refl
  (λ m e → cong suc e)
  n

indBool : (P : Bool → Set) → P true → P false → (b : Bool) → P b
indBool P t f true = t
indBool P t f false = f

open import Lib.Containers.List

indList : {A : Set}(P : List A → Set) → P [] → ((a : A)(as : List A) → P as → P (a ∷ as)) →
  (as : List A) → P as
indList P n c [] = n
indList P n c (a ∷ as) = c a as (indList P n c as)

-- subst, transport
ite≡ : {A : Set}{a : A} → (E : A → Set) → E a → {b : A} → a ≡ b → E b
ite≡ E u refl = u

ind≡ : {A : Set}{a : A}(P : {b : A} → a ≡ b → Set) → P refl → {b : A}(e : a ≡ b) → P e
ind≡ P u refl = u
