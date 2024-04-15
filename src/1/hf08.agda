module hf08 where

open import Lib

--------------------------------------------------------------
-- Elméleti rész -- formalizálás első rendben.
--------------------------------------------------------------

module Universe
  (Élőlény : Set)
  (Rovar : Élőlény → Set)
  (Bogár : Élőlény → Set)
  (Kitines : Élőlény → Set)
  (Szarvasbogár : Élőlény → Set)
  (legjobbBarát : Élőlény → Élőlény)
  (Szarvas : Élőlény)
  (_===_ : Élőlény → Élőlény → Set)
  where

  -- Minden bogár rovar, de nem minden rovar bogár.
  Állítás1 : Set
  Állítás1 = {!   !}

  -- Szarvasnak, a szarvasbogárnak kitines a szárnyfedője.
  Állítás2 : Set
  Állítás2 = {!   !}

  -- Egy rovarnak nincs kitines szárnyfedője vagy bogár.
  Állítás3 : Set
  Állítás3 = {!   !}

  -- Szarvas legjobb barátja bogár.
  Állítás4 : Set
  Állítás4 = {!   !}

  -- Van olyan rovar, akinek a legjobb barátja szarvasbogár.
  Állítás5 : Set
  Állítás5 = {!   !}


  -- Van két olyan bogár, akik a legjobb barátai egymásnak.
  Állítás6 : Set
  Állítás6 = {!   !}

--------------------------------------------------------------------
-- Gyakorlati rész
--------------------------------------------------------------------

-- Továbbá az alja Dec-es részből is érdemes bizonyításokat csinálni, főleg az addF és removeF-et.

{-
Bizonyítsd be, hogy ha ∃a(P(a) ∨ Q(a)) akkor és csak akkor, ha ∃aP(a) ∨ ∃aQ(a)
-}
Σ⊎-distr : (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a)  ↔ Σ A P ⊎ Σ A Q
Σ⊎-distr = {!!}

{-
Bizonyítsd be, hogy ha ∃a¬P(a), akkor ¬∀aP(a)
-}
¬∀ : (A : Set)(P : A → Set) → (Σ A λ a → ¬ P a) → ¬ ((a : A) → P a)
¬∀ = {!   !}

{-
Bizonyítsd be, hogy ha ¬∃aP(a), akkor ∀a¬P(a)
-}
¬Σ : (A : Set)(P : A → Set) → (¬ Σ A λ a → P a) ↔ ((a : A) → ¬ P a)
¬Σ = {!   !}

{-
Bizonyítsd be, hogy ha ¬¬∀aP(a), akkor ∀a¬¬P(a)
-}
¬¬∀-nat : (A : Set)(P : A → Set) → ¬ ¬ ((x : A) → P x) → (x : A) → ¬ ¬ (P x)
¬¬∀-nat = {!   !}


Σ∀ : (A B : Set)(R : A → B → Set) → (Σ A λ x → (y : B) → R x y) → (y : B) → Σ A λ x → R x y
Σ∀ = {!   !}

{-
Axiom of chioce = kiválasztási axióma:
Bizonyítsd, hogy ha ∀x∃yR(x,y), akkor ∃f∀xR(x,f(x)).
-}
AC : (A B : Set)(R : A → B → Set) → ((x : A) → Σ B λ y → R x y) → Σ (A → B) λ f → (x : A) → R x (f x)
AC = {!   !}

--------------------------
{-
Döntsd el, hogy két azonos kvantor változói felcserélhetők-e vagy nem.
-}
∀∀ : Dec ((A B : Set)(R : A → B → Set) → (∀ a → ∀ b → R a b) → (∀ b → ∀ a → R a b))
∀∀ = {!   !}

ΣΣ : Dec ((A B : Set)(R : A → B → Set) → (Σ A λ a → Σ B λ b → R a b) → Σ B λ b → Σ A λ a → R a b)
ΣΣ = {!   !}

-- NEHÉZ FELADAT (lentebb még vannak nem nehézként megjelölt feladatok)
{-
A ∃-et fel lehet cserélni a ∀-nel, ha a ∃ kívül van. Ugyanazon érvelés miatt,
mint a ∀ a vagyot, vagy épp a ∃ az ést kevésbé szereti, itt is ez a helyzet.
Döntsd el, hogy teljesül-e az állítás, majd bizonyítsd vagy cáfold!
-}
∀Σ : Dec ((A B : Set)(R : A → B → Set) → ((y : B) → Σ A λ x → R x y) → (Σ A λ x → (y : B) → R x y))
∀Σ = {!   !}

{-
Döntsd el, hogy az alábbi állítások igazak-e vagy sem.
Bizonyítsd vagy cáfold!
-}
→∀ : Dec ((A : Set)(P : A → Set)(Q : A → Set) → ((∀ x → P x) → (∀ x → Q x)) → ∀ x → P x → Q x)
→∀ = {!   !}

∀→ : Dec ((A : Set)(P : A → Set)(Q : A → Set) → (∀ x → P x → Q x) → (∀ x → P x) → ∀ x → Q x)
∀→ = {!   !}

∃→ : Dec ((A : Set)(P : A → Set)(Q : A → Set) → Σ A (λ x → P x → Q x) → Σ A P → Σ A Q)
∃→ = {!   !}

→∃ : Dec ((A : Set)(P : A → Set)(Q : A → Set) → (Σ A P → Σ A Q) → Σ A (λ x → P x → Q x))
→∃ = {!   !}

addF : Dec ((A : Set)(P : A → Set)(f : A → A) → (∀ x → P x) → ∀ x → P (f x))
addF = {!   !}

removeF : Dec ((A : Set)(P : A → Set)(f : A → A) → (∀ x → P (f x)) → ∀ x → P x)
removeF = {!   !}
