module hf09 where

open import lib

-- Órai feladatok

Dec : ∀{i} → Set i → Set i
Dec A = A ⊎ ¬ A

{-
Bizonyítsd be, hogy ha ∃aP(a) ∧ ∃aQ(a), az még nem jelenti azt, hogy ∃a(P(a) ∧ Q(a))
a with használata nélkül.
A gyakorlaton látott ötlet megfelelő, csak használjuk hozzá az indℕ függvényt,
hogy ne leak-eljük a P és Q implementációját.
-} 

indℕ : (n : ℕ)(P : ℕ → Set) → P 0 → ((k : ℕ) → P k → P (suc k)) → P n
indℕ zero P p0 f = p0
indℕ (suc n) P p0 f = f n (indℕ n P p0 f)

Σ×-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (Σ A P × Σ A Q → Σ A λ a → P a × Q a))
Σ×-distr' w = let (n , pn , qn) = w ℕ P Q ((0 , tt) , (1 , tt)) in {!   !} where
  P : ℕ → Set
  P zero = ⊤
  P (suc n) = ⊥

  Q : ℕ → Set
  Q zero = ⊥
  Q (suc n) = ⊤
{-
A többi feladatban értelemszerűen lehet nyugodtan with-et használni,
ha úgy jön ki kényelmesebben!
-}


{-
A ∀ az × műveletet szereti, bizonyítsd be, hogy a ∀a(P(a) ∧ Q(a))-t fel lehet bontani
∀aP(a) ∧ ∀aQ(a)-ra, illetve össze is lehet vonni.
-}
∀×-distr : (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
∀×-distr = {!!}

{-
Ahogy a ∃ nem szereti az ést, úgy a ∀ nem szereti a vagyot, de az egyik irány
működik, ahogy a ∃ esetében is. A ∃ esetében szét lehetett szedni az ést,
a ∀ esetében a vagyot viszont összerakni lehet.
Bizonyítsd be, hogy összerakni össze lehet, viszont szétszedni nem.
-}
∀⊎-distr : (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a) ⊎ ((a : A) → Q a) → ((a : A) → P a ⊎ Q a)
∀⊎-distr = {!!}

∀⊎-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (((a : A) → P a ⊎ Q a) → ((a : A) → P a) ⊎ ((a : A) → Q a)))
∀⊎-distr' = {!!}

{-
Bizonyítsd be, hogy ha ∃a¬P(a), akkor ¬∀aP(a)
-}
¬∀ : (A : Set)(P : A → Set) → (Σ A λ a → ¬ P a) → ¬ ((a : A) → P a)
¬∀ = {!!}

{-
Bizonyítsd be, hogy ha ¬∃aP(a), akkor ∀a¬P(a)
-}
¬Σ : (A : Set)(P : A → Set) → (¬ Σ A λ a → P a) ↔ ((a : A) → ¬ P a)
¬Σ = {!!}

{-
Bizonyítsd be, hogy ha ¬¬∀aP(a), akkor ∀a¬¬P(a)
-}
¬¬∀-nat : (A : Set)(P : A → Set) → ¬ ¬ ((x : A) → P x) → (x : A) → ¬ ¬ (P x)
¬¬∀-nat = {!!}


Σ∀ : (A B : Set)(R : A → B → Set) → (Σ A λ x → (y : B) → R x y) → (y : B) → Σ A λ x → R x y
Σ∀ = {!!}

{-
Axiom of chioce = kiválasztási axióma:
Bizonyítsd, hogy ha ∀x∃yR(x,y), akkor ∃f∀xR(x,f(x)).
-}
AC : (A B : Set)(R : A → B → Set) → ((x : A) → Σ B λ y → R x y) → Σ (A → B) λ f → (x : A) → R x (f x)
AC = {!   !}

--------------------------
{-
Ahogy a természetes számoknál is, a Bool-oknál is szükség van
egy okosabb if-then-else-re, ami tartalmazza is az információt, hogy
melyik ágon volt a feltétel igaz, illetve hamis.
Ennek a definíciója a típus miatt teljesen egyértelmű és nem lehet
elrontani (míg ugye az if-then-else-et igen).
-}
indBool : ∀{i}{A : Bool → Set i}(b : Bool) → A true → A false → A b
indBool b tr fa = {!   !}

-- NEHÉZ FELADAT (lentebb még vannak nem nehézként megjelölt feladatok)
{-
A ∃-et fel lehet cserélni a ∀-nel, ha a ∃ kívül van. Ugyanazon érvelés miatt,
mint a ∀ a vagyot, vagy épp a ∃ az ést kevésbé szereti, itt is ez a helyzet.
Ha a ∀ van kívül és a ∃ belül, akkor nem lehet felcserélni azokat.
Bizonyítsd ezt be!
-}
∀Σ : ¬ ((A B : Set)(R : A → B → Set) → ((y : B) → Σ A λ x → R x y) → (Σ A λ x → (y : B) → R x y))
∀Σ = {!   !}

{-
Döntsd el, hogy két azonos kvantor változói felcserélhetők-e vagy nem.
-}

∀∀ : Dec ((A B : Set)(R : A → B → Set) → (∀ a → ∀ b → R a b) → (∀ b → ∀ a → R a b))
∀∀ = {!   !}

ΣΣ : Dec ((A B : Set)(R : A → B → Set) → (Σ A λ a → Σ B λ b → R a b) → Σ B λ b → Σ A λ a → R a b)
ΣΣ = {!   !}

{-
Döntsd el, hogy az alábbi állítások igazak-e vagy sem.
Bizonyítsd vagy cáfold!
-}

∀→ : Dec ((A : Set)(P : A → Set)(Q : A → Set) → (∀ x → P x → Q x) → (∀ x → P x) → ∀ x → Q x)
∀→ = {!   !}

→∀ : Dec ((A : Set)(P : A → Set)(Q : A → Set) → ((∀ x → P x) → (∀ x → Q x)) → ∀ x → P x → Q x)
→∀ = {!   !}

∃→ : Dec ((A : Set)(P : A → Set)(Q : A → Set) → Σ A (λ x → P x → Q x) → Σ A P → Σ A Q)
∃→ = {!   !}

-- NEHÉZ FELADAT
→∃ : Dec ((A : Set)(P : A → Set)(Q : A → Set) → (Σ A P → Σ A Q) → Σ A (λ x → P x → Q x))
→∃ = {!   !}

addF : Dec ((A : Set)(P : A → Set)(f : A → A) → (∀ x → P x) → ∀ x → P (f x))
addF = {!   !}

removeF : Dec ((A : Set)(P : A → Set)(f : A → A) → (∀ x → P (f x)) → ∀ x → P x)
removeF = {!   !}