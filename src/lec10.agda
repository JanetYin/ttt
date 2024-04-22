{-# OPTIONS --without-K #-}

module lec10 where

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

{-
open import Lib

-- data _≡_ {A : Set}(a : A) : A → Set where
-- a ≡_ : A → Set, this is the predicate which says "equal to a"
-- 3 ≡_ : ℕ → Set meaning "equal to 3"
-- true ≡_ : Bool → Set
-- (2 , false) ≡_ : ℕ × Bool → Set
-- (1 ∷ 2 ∷ 3 ∷ []) ≡_ : List ℕ → Set
-- _≡_ {A = ℕ → ℕ} (λ x → x) : (ℕ → ℕ) → Set
-- ℕ ≡_ : Set → Set  <- this is a predicate on types saying that a type is equal to ℕ

cong' : {A B : Set}(f : A → B){a a' : A} → a ≡ a' → f a ≡ f a'
cong' f refl = refl

uncong' : {A B : Set}(f : A → B){a a' : A} → f a ≡ f a' → a ≡ a'
uncong' f e = {!e!} -- not every function is injective

¬uncong : ¬ ({A B : Set}(f : A → B){a a' : A} → f a ≡ f a' → a ≡ a')
¬uncong H = 0≠1 w
  where
    w : 0 ≡ 1
    w = H {ℕ}{ℕ}(λ _ → 0) {0}{1} refl
    0≠1 : ¬ (_≡_ {A = ℕ} 0 1)
    0≠1 ()

¬uncong' : ¬ ({A B : Set}(f : A → B){a a' : A} → f a ≡ f a' → a ≡ a')
¬uncong' H with H {ℕ}{ℕ}(λ _ → 0) {0}{1} refl
... | ()
-- ¬uncong' means ¬uncong

decEq : (a b : ℕ) → a ≡ b ⊎ ¬ (a ≡ b)  -- equality of ℕ is decidable, law of excluded middle holds for equality of ℕ
decEq zero zero = inl refl
decEq zero (suc b) = inr (λ ())
decEq (suc a) zero = inr (λ ())
decEq (suc a) (suc b) with decEq a b
... | inl refl = inl refl
... | inr ne = inr λ { refl → ne refl }
{-
decEq (suc a) (suc b) = case (decEq a b)
--   (λ e → inl (cong suc e))
  (λ { refl → inl refl })
  (λ ne → inr λ { refl → ne refl })
-}

coe : {A B : Set} → A ≡ B → A → B
coe refl a = a

-- we proved that it is not the case that every function is injective, but some are.

sucinj : {m n : ℕ} → suc m ≡ suc n → m ≡ n
sucinj e = cong pred' e

-- more generally, every constructor of every inductive type is injective

coeinj : {A B : Set}(e : A ≡ B){a a' : A} → coe e a ≡ coe e a' → a ≡ a'
coeinj refl e' = e'

-- coercion is also injective

NatNotTop : ℕ ≡ ⊤ → 0 ≡ 1
NatNotTop e = coeinj e {0}{1} e'
  where
    e' : coe e 0 ≡ coe e 1
    e' = refl

NatNotTop' : ¬ (ℕ ≡ ⊤)
NatNotTop' e with NatNotTop e
... | ()
-}
-- in ordinary Agda I can prove this
UIP UIP' : {A : Set}(a b : A)(p q : a ≡ b) → p ≡ q
UIP a .a refl e = {!e!}

ind≡ : {A : Set}{a : A}(P : {b : A} → a ≡ b → Set) → P refl → {b : A}(e : a ≡ b) → P e
ind≡ P u refl = u

UIP' {A} a b p q = {!ind≡!}

-- UIP cannot be proven from ind≡

-- the other induction principle that they added to type theory in 1996 in order to prove UIP
-- ind≡' = K : {A : Set}{a : A}(P : a ≡ a → Set) → P refl → (e : a ≡ a) → P e

{-
              observational type theory (this fixes equality of functions)
                ^
               /
             UIP (adding K to type theory)
             ^
            /
type theory
--without-K
            \
             v
            univalence = equality of Set is bijection, HoTT(homotopy type theory) = Cubical Agda
            --cubical
-}


-- e : ℕ ≡ ⊤        e : A ≡ B
-- n : ℕ            a : A
-------------       -----------
-- ... : ⊤          coe e a : B  -- coercion

-- e : ℕ ≡ ⊤
---------------
-- refl : coe e 0 ≡ tt
-- refl : coe e 1 ≡ tt
-- refl : coe e 0 ≡ coe e 1

-- tt : ⊤
---------------------
-- coe (sym e) tt : ℕ
