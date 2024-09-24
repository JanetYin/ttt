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

  -- -- Minden bogár rovar, de nem minden rovar bogár.
  -- Állítás1 : Set
  -- Állítás1 = {!   !}

  -- -- Szarvasnak, a szarvasbogárnak kitines a szárnyfedője.
  -- Állítás2 : Set
  -- Állítás2 = {!   !}

  -- -- Egy rovarnak nincs kitines szárnyfedője vagy bogár.
  -- Állítás3 : Set
  -- Állítás3 = {!   !}

  -- -- Szarvas legjobb barátja bogár.
  -- Állítás4 : Set
  -- Állítás4 = {!   !}

  -- -- Van olyan rovar, akinek a legjobb barátja szarvasbogár.
  -- Állítás5 : Set
  -- Állítás5 = {!   !}


  -- -- Van két olyan bogár, akik a legjobb barátai egymásnak.
  -- Állítás6 : Set
  -- Állítás6 = {!   !}

--------------------------------------------------------------------
-- Gyakorlati rész
--------------------------------------------------------------------

-- Továbbá az alja Dec-es részből is érdemes bizonyításokat csinálni, főleg az addF és removeF-et.

{-
Bizonyítsd be, hogy ha ∃a(P(a) ∨ Q(a)) akkor és csak akkor, ha ∃aP(a) ∨ ∃aQ(a)
-}
Σ⊎-distr : (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a)  ↔ Σ A P ⊎ Σ A Q
fst (Σ⊎-distr A P Q) (fst₁ , inl a) = inl (fst₁ , a)
fst (Σ⊎-distr A P Q) (fst₁ , inr b) = inr (fst₁ , b)
snd (Σ⊎-distr A P Q) (inl a) = (fst a) , (inl (snd a))
snd (Σ⊎-distr A P Q) (inr b) = (fst b) , (inr (snd b))

{-
Bizonyítsd be, hogy ha ∃a¬P(a), akkor ¬∀aP(a)
-}
¬∀ : (A : Set)(P : A → Set) → (Σ A λ a → ¬ P a) → ¬ ((a : A) → P a)
¬∀ A P x x₁ = snd x (x₁ (fst x))

{-
Bizonyítsd be, hogy ha ¬∃aP(a), akkor ∀a¬P(a)
-}
¬Σ : (A : Set)(P : A → Set) → (¬ Σ A λ a → P a) ↔ ((a : A) → ¬ P a)
fst (¬Σ A P) x a x₁ = x (a , x₁)
snd (¬Σ A P) x x₁ = x (fst x₁) (snd x₁)

{-
Bizonyítsd be, hogy ha ¬¬∀aP(a), akkor ∀a¬¬P(a)
-}
¬¬∀-nat : (A : Set)(P : A → Set) → ¬ ¬ ((x : A) → P x) → (x : A) → ¬ ¬ (P x)
¬¬∀-nat A P x x₁ x₂ = x (λ x₃ → x₂ (x₃ x₁))


Σ∀ : (A B : Set)(R : A → B → Set) → (Σ A λ x → (y : B) → R x y) → (y : B) → Σ A λ x → R x y
Σ∀ A B R x y = (fst x) , (snd x y)

{-
Axiom of chioce = kiválasztási axióma:
Bizonyítsd, hogy ha ∀x∃yR(x,y), akkor ∃f∀xR(x,f(x)).
-}
AC : (A B : Set)(R : A → B → Set) → ((x : A) → Σ B λ y → R x y) → Σ (A → B) λ f → (x : A) → R x (f x)
AC A B R x = (λ x₁ → fst (x x₁)) , (λ x₁ → snd (x x₁))

--------------------------
{-
Döntsd el, hogy két azonos kvantor változói felcserélhetők-e vagy nem.
-}
∀∀ : Dec ((A B : Set)(R : A → B → Set) → (∀ a → ∀ b → R a b) → (∀ b → ∀ a → R a b))
∀∀ = inl (λ A B R x b a → x a b)

ΣΣ : Dec ((A B : Set)(R : A → B → Set) → (Σ A λ a → Σ B λ b → R a b) → Σ B λ b → Σ A λ a → R a b)
ΣΣ = inl (λ A B R x → (fst (snd x)) , ((fst x) , (snd  (snd x))))

-- NEHÉZ FELADAT (lentebb még vannak nem nehézként megjelölt feladatok)
{-
A ∃-et fel lehet cserélni a ∀-nel, ha a ∃ kívül van. Ugyanazon érvelés miatt,
mint a ∀ a vagyot, vagy épp a ∃ az ést kevésbé szereti, itt is ez a helyzet.
Döntsd el, hogy teljesül-e az állítás, majd bizonyítsd vagy cáfold!
-}

noall : ¬ ( ((A B : Set) (R : A → B → Set) →
       ((y : B) → Σ A (λ x → R x y)) → Σ A (λ x → (y : B) → R x y))) 
noall x with x A B R p1
  where 
    A B : Set 
    A = ⊥
    B = ⊥
    R : A → B → Set
    R x x₁ = ⊥
    p1 : (y : B) → Σ A (λ x → R x y)
    p1 ()
...| y = fst y
∀Σ : Dec ((A B : Set)(R : A → B → Set) → ((y : B) → Σ A λ x → R x y) → (Σ A λ x → (y : B) → R x y))
∀Σ = inr noall 
  
{-
Döntsd el, hogy az alábbi állítások igazak-e vagy sem.
Bizonyítsd vagy cáfold!
-}
no→∀ :  ¬ ((A : Set) (P Q : A → Set) →  (((x : A) → P x) → (x : A) → Q x) → (x : A) → P x → Q x)
no→∀ x with x A P Q p1 false tt
  where 
    A : Set 
    A = Bool 
    P Q : A → Set
    P false = ⊤
    P true = ⊥
    Q false = ⊥
    Q true = ⊤
    p1 : ((x : A) → P x) → (x : A) → Q x
    p1 x false = x true
    p1 x true = tt
...| y = y


→∀ : Dec ((A : Set)(P : A → Set)(Q : A → Set) → ((∀ x → P x) → (∀ x → Q x)) → ∀ x → P x → Q x)
→∀ = inr no→∀ 
  
∀→ : Dec ((A : Set)(P : A → Set)(Q : A → Set) → (∀ x → P x → Q x) → (∀ x → P x) → ∀ x → Q x)
∀→ = inl (λ A P Q x x₁ x₂ → x x₂ (x₁ x₂))

noe : ¬ ((A : Set) (P Q : A → Set) → Σ A (λ x → P x → Q x) → Σ A P → Σ A Q)
noe x with x A P Q p1 p2
  where
    A : Set 
    A = Bool 
    P Q : A → Set 
    P false =  ⊤
    P true = ⊥
    Q false = ⊥
    Q true = ⊥
    p2 : Σ A P
    p2 = false , tt
    p1 : Σ A (λ x → P x → Q x)
    p1 = true , (λ {()})
... | false , snd₁ = snd₁
... | true , snd₁ = snd₁

∃→ : Dec ((A : Set)(P : A → Set)(Q : A → Set) → Σ A (λ x → P x → Q x) → Σ A P → Σ A Q)
∃→ = inr noe 

no→e : ¬ ((A : Set) (P Q : A → Set) →  (Σ A P → Σ A Q) → Σ A (λ x → P x → Q x))
no→e x with x A P Q p1  
  where 
    A : Set 
    A = ⊥
    P Q : A → Set
    P ()
    Q ()
    p1 : Σ A P → Σ A Q 
    p1 () 
... | y = fst y

→∃ : Dec ((A : Set)(P : A → Set)(Q : A → Set) → (Σ A P → Σ A Q) → Σ A (λ x → P x → Q x))
→∃ = inr no→e

addF : Dec ((A : Set)(P : A → Set)(f : A → A) → (∀ x → P x) → ∀ x → P (f x))
addF = inl (λ A P f x x₁ → x (f x₁))

norev : ¬ ((A : Set)(P : A → Set)(f : A → A) → (∀ x → P (f x)) → ∀ x → P x)
norev x with x A P f p1 false 
  where 
    A : Set 
    A = Bool
    P : A → Set
    P false = ⊥
    P true = ⊤
    f : A → A
    f false = true
    f true = true
    p1 : ∀ x → P (f x) 
    p1 false = tt
    p1 true = tt
...| y = y
removeF : Dec ((A : Set)(P : A → Set)(f : A → A) → (∀ x → P (f x)) → ∀ x → P x)
removeF = inr norev 