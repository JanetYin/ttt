module ea09 where

open import lib

-- vizsgak: minden kedden 10-12 kozott, gepteremben

-- Ez az előadás 13 perccel rövidebb.

-- data _≡_                      : ℕ → ℕ → Set where
--   refl : (m : ℕ) → m ≡ m
-- data _≡_            (x : ℕ)   : ℕ → Set     where
--   refl : x ≡ x
-- data _≡_  {A : Set} (x : A)   : A → Set     where
-- data List (A : Set)           : Set         where
--   cons : A → List A → List A
-- data Vec  (A : Set)           : ℕ → Set     where
-- data _≤_                      : ℕ → ℕ → Set where
--   0≤ : (m : ℕ) → 0 ≤ m
--   s≤ : {m n : ℕ} → m ≤ n → suc m ≤ suc n
-- data TreeWithHeight (A : Set) : ℕ → Set     where
--   leaf : A → TreeWithHeight A 0
--   node : {m n : ℕ} → TreeWithHeight A m → TreeWithHeight A n →
--          TreeWithHeight A (max m n)

-- volt refl, sym : x ≡ y → y ≡ x,
-- trans : x ≡ y → y ≡ z → x ≡ z,
-- trans : x ≡ z → x ≡ z,
-- trans : x ≡ z → x ≡ z,
-- cong  : x ≡ y → f x ≡ f y
-- subst : (P : A → Set) → x ≡ y → P x → P y
-- subst (Vec Bool) : m ≡ n → Vec m → Vec n  -- P egy tipuscsalad
-- subst (Vec Bool) : 3 ≡ n → Vec 3 → Vec n
-- subst (_> 4) : m ≡ n → m > 4 → n > 4
-- subst (_≡ 4) : m ≡ n → m ≡ 4 → n ≡ 4
-- subst (λ x → x ≡ 4) : m ≡ n → m ≡ 4 → n ≡ 4

cong : {A B : Set}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f {x} refl = refl {x = f x}

-- subst         (λ x → P x) : m ≡ n → P m → P n
--
--                              m ≡ n → m ≡ m → n ≡ m
-- subst {m}{n} (λ n → n ≡ m) : m ≡ n → P m   → P n

-- HF: megadni subst-al sym, trans, cong

-- Bool eliminatora if-then-else-, iteBool, caseBool
-- ℕ eliminatora a iteNat, recNat
-- _≡_ eliminatora a subst, ite≡, rec≡, case≡ (szinte)

-- prop vs defn eq, kviz

-- 3 + 0 = 3 IGAZ
-- x + 0 = x NEM IGAZ
-- 0 + x = x IGAZ

-- refl : 3 + 0 ≡ 3    IGAZ
--- ?   : x + 0 ≡ x    IGAZ
{-
Agda-ban ketfele egyenloseg van:
= definicionalis egyenloseg,  egyenloseg-itelet     automatikus,
                                                    Agda helyettunk belatja
                                                    errol nem beszelhetunk:
                                                    NEM AGDA-BELI TIPUS
                                                    ad-hoc
                                                    if x then a else a ≠ a
                                                    IGAZ: Agda szabalyai alapjan
                                                          kijon (→β, ⇒η, definiciok feloldasa)
                                                          vegrehajtjuk a programot, es
                                                          megnezzuk, hogy egyenlok-e
                                                    eldontheto
≡ propozicionalis egyenloseg, egyenloseg tipus      IGAZI EGYENLOSEG
                                                    matematikai egyenloseg
                                                    Agda-n belul van, bizonyithato
                                                    nem ad-hoc
                                                    if x then a else a ≡ a
                                                    IGAZ = van ilyen tipusu term
                                                         = van ennek bizonyitasa Agdaban
                                                    nem eldontheto
-}

-- indukcio, + idl, idr, assoc, comm

idl : (m : ℕ) → 0 + m ≡ m
idl m = refl
{-
trues : (n : ℕ) → Vec Bool n
trues zero = []
trues (suc n) = true ∷ trues n
-}
idr : (m : ℕ) → m + 0 ≡ m
idr zero    = refl
idr (suc n) = cong suc (idr n)
-- idr (suc n) = cong suc (idr n)

-- teljes indukcio: ha be akarom latni, hogy
indℕ : (P : ℕ → Set) → P 0 → ({m : ℕ} → P m → P (1 + m)) → (n : ℕ) → P n
indℕ P z s zero    = z
indℕ P z s (suc n) = s (indℕ P z s n)
-- teljes indukcio, ez az ℕ tipus fuggo eliminatora. ez a recℕ fuggo valtozata
-- HF: add meg recℕ-t indℕ segitsegevel mintaillesztes nelkul

idr' : (m : ℕ) → m + 0 ≡ m
idr' = indℕ (λ m → m + 0 ≡ m) refl (cong suc)

assoc : (m n o : ℕ) → (m + n) + o ≡ m + (n + o)
assoc zero    n o = refl
assoc (suc m) n o = cong suc (assoc m n o)

-- ℕ a 0-val es _+_-al egysegelemes felcsoport (monoid)

-- igazabol ez kommutativ monoidot alkot
comm : (m n : ℕ) → m + n ≡ n + m
comm = {!!}


-- klassz vs konstr
