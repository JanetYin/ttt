module hf06 where

open import Lib hiding (_≤ℕ_; _≥ℕ_; _≡ℕ_; reflℕ; min; max)
open import Lib.Containers.Vector

-- Az alján a "half" nevű függvényt érdemes megcsinálni!

even : ℕ → Bool
even 0 = true
even 1 = false
even (suc (suc n)) = even n

--------------------------------------------------------

{-
Definiáld a _≤_ és _≥_ függvényeket, amelyek rendre meghatározzák
típusszinten, hogy az első szám kisebbegyenlő, illetve nagyobbegyenlő,
mint a másik szám.
-}
infix 4 _≤ℕ_
_≤ℕ_ : ℕ → ℕ → Set
_≤ℕ_ = {!   !}

≤-test1 : (λ x → 0 ≤ℕ x) ≡ (λ x → ⊤)
≤-test1 = refl

≤-test2 : 3 ≤ℕ 10
≤-test2 = tt

≤-test3 : ¬ (10 ≤ℕ 3)
≤-test3 ()

infix 4 _≥ℕ_
_≥ℕ_ : ℕ → ℕ → Set
_≥ℕ_ = {!   !}

≥-test1 : (λ x → x ≥ℕ 0) ≡ (λ x → ⊤)
≥-test1 = refl

≥-test2 : 30 ≥ℕ 10
≥-test2 = tt

≥-test3 : ¬ (10 ≥ℕ 30)
≥-test3 ()

{-
Definiáld a _≡ℕ_ függvényt, amely típusszinten meghatározza, hogy
két természetes szám egyenlő egymással.
-}
infix 4 _≡ℕ_
_≡ℕ_ : ℕ → ℕ → Set
_≡ℕ_ = {!   !}

≡ℕ-test1 : 3 ≡ℕ 3
≡ℕ-test1 = tt

≡ℕ-test2 : ¬ (3 ≡ℕ 4)
≡ℕ-test2 ()

≡ℕ-test3 : (4 ≡ℕ 3) ≡ ⊥
≡ℕ-test3 = refl

{-
Bizonyítsd, hogy az ≡ℕ művelet reflexív!
-}
reflℕ : (n : ℕ) → n ≡ℕ n
reflℕ = {!   !}

{-
Definiáld a min és a max függvényt, amely két szám közül rendre a kisebbet, illetve
a nagyobbat adja vissza és mellette egy bizonyítást, hogy a jót adja vissza.
A függőtípusokkal egy teljes specifikációját le lehet írni a függvénynek,
ez van most a min és a max függvényekben megadva.
Olvasva a következő a specifikáció:
Előfeltétel: Van két tetszőleges ℕ számom.
Utófeltétel: Létezik olyan (n : ℕ) szám, amelyre teljesül, hogy:
  -- ha x ≤ y, akkor x megegyezik n-nel
  VAGY
  -- ha x ≥ y, akkor y megegyezik n-nel
-}
min : (x y : ℕ) → Σ ℕ (λ n → x ≤ℕ y × x ≡ℕ n ⊎ x ≥ℕ y × y ≡ℕ n)
min = {!   !}

min-test1 : fst (min 3 6) ≡ 3
min-test1 = refl

min-test2 : fst (min 6 4) ≡ 4
min-test2 = refl

min-test3 : fst (min 5 5) ≡ 5
min-test3 = refl

max : (x y : ℕ) → Σ ℕ (λ n → x ≥ℕ y × x ≡ℕ n ⊎ x ≤ℕ y × y ≡ℕ n)
max = {!   !}

max-test1 : fst (max 3 6) ≡ 6
max-test1 = refl

max-test2 : fst (max 6 4) ≡ 6
max-test2 = refl

max-test3 : fst (max 5 5) ≡ 5
max-test3 = refl

{-
Definiáld a takeWhile függvényt, amely addig tartja meg egy vektor elemeit,
amíg a feltétel teljesül.
-}
takeWhile : ∀{i}{A : Set i}{n : ℕ} → (A → Bool) → Vec A n → Σ ℕ (Vec A)
takeWhile = {!   !}

takeWhile-test1 : takeWhile even (2 ∷ 4 ∷ 0 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (3 , 2 ∷ 4 ∷ 0 ∷ [])
takeWhile-test1 = refl

takeWhile-test2 : takeWhile even (1 ∷ 2 ∷ 3 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (0 , [])
takeWhile-test2 = refl

takeWhile-test3 : takeWhile (0 <ᵇ_) (1 ∷ 2 ∷ 3 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (6 , 1 ∷ 2 ∷ 3 ∷ 3 ∷ 4 ∷ 5 ∷ [])
takeWhile-test3 = refl

takeWhile-test4 : takeWhile (0 <ᵇ_) (0 ∷ 1 ∷ 2 ∷ 4 ∷ 5 ∷ []) ≡ (0 , [])
takeWhile-test4 = refl

{-
Egészítsd ki a takeWhile definícióját egy bizonyítással, amely azt mondja,
hogy az eredmény elemszáma legfeljebb n.
-}

takeWhile' : ∀{i}{A : Set i}{n : ℕ} → (A → Bool) → Vec A n → Σ ℕ (λ x → Vec A x × x ≤ℕ n)
takeWhile' = {!   !}

takeWhile'-test1 : takeWhile' even (2 ∷ 4 ∷ 0 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (3 , 2 ∷ 4 ∷ 0 ∷ [] , tt)
takeWhile'-test1 = refl

takeWhile'-test2 : takeWhile' even (1 ∷ 2 ∷ 3 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (0 , [] , tt)
takeWhile'-test2 = refl

takeWhile'-test3 : takeWhile' (0 <ᵇ_) (1 ∷ 2 ∷ 3 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (6 , 1 ∷ 2 ∷ 3 ∷ 3 ∷ 4 ∷ 5 ∷ [] , tt)
takeWhile'-test3 = refl

takeWhile'-test4 : takeWhile' (0 <ᵇ_) (0 ∷ 1 ∷ 2 ∷ 4 ∷ 5 ∷ []) ≡ (0 , [] , tt)
takeWhile'-test4 = refl

{-
Definiáld a span függvényt, amely egy vektort két részre bont azon a ponton, ahol
egy adott tulajdonság már nem teljesül.
-}
span : ∀{i}{A : Set i}{n : ℕ} → (p : A → Bool) → Vec A n → Σ ℕ (λ x → Σ ℕ (λ y → Vec A x × Vec A y × x + y ≡ℕ n))
span = {!   !}

span-test1 : span even (2 ∷ 4 ∷ 1 ∷ []) ≡ (2 , 1 , 2 ∷ 4 ∷ [] , 1 ∷ [] , tt)
span-test1 = refl

span-test2 : span (_<ᵇ 3) (2 ∷ 4 ∷ 1 ∷ []) ≡ (1 , 2 , 2 ∷ [] , 4 ∷ 1 ∷ [] , tt)
span-test2 = refl

span-test3 : span {_} {ℕ} (λ _ → false) (2 ∷ 4 ∷ 1 ∷ []) ≡ (0 , 3 , [] , 2 ∷ 4 ∷ 1 ∷ [] , tt)
span-test3 = refl

span-test4 : span {_} {ℕ} (λ _ → true) (2 ∷ 4 ∷ 1 ∷ []) ≡ (3 , 0 , 2 ∷ 4 ∷ 1 ∷ [] , [] , tt)
span-test4 = refl

-- Bizonyítsd be az alábbi állítást:
ΣΣ=Σ× : ∀{i j k}{A : Set i}{B : Set j}(P : A → B → Set k) → (Σ A (λ a → Σ B (λ b → P a b))) ↔ (Σ (A × B) (λ (a , b) → P a b))
ΣΣ=Σ× P = {!   !}

-- Ezt a feladatot érdemes megcsinálni!
-- Definiáld a half∞ függvényt, amely egy kotermészetes számot megfelez, annak az alsó egész részét visszaadva.
half∞ : ℕ∞ → ℕ∞
half∞ = ?

half∞-test1 : ℕ∞→ℕ 50 (half∞ 10) ≡ just 5
half∞-test1 = refl
half∞-test2 : ℕ∞→ℕ 50 (half∞ 11) ≡ just 5
half∞-test2 = refl
half∞-test3 : ℕ∞→ℕ 50 (half∞ 12) ≡ just 6
half∞-test3 = refl
half∞-test4 : ℕ∞→ℕ 50 (half∞ 0) ≡ just 0
half∞-test4 = refl
half∞-test5 : ℕ∞→ℕ 50 (half∞ 1) ≡ just 0
half∞-test5 = refl

-- NEHÉZ FELADAT
-- Definiáld a _<ℕ∞_ függvényt, amely egy természetes számot és egy
-- kotermészetes számot összehasonlít, megvizsgálja, hogy a természetes szám
-- kisebb-e, mint a kotermészetes.
infix 4 _<ℕ∞_
_<ℕ∞_ : ℕ → ℕ∞ → Set
_<ℕ∞_ = ?

<ℕ∞-test1 : (9 <ℕ∞ 10) ≡ ⊤
<ℕ∞-test1 = refl
<ℕ∞-test2 : (9 <ℕ∞ 9) ≡ ⊥
<ℕ∞-test2 = refl
<ℕ∞-test3 : (9 <ℕ∞ 8) ≡ ⊥
<ℕ∞-test3 = refl
<ℕ∞-test4 : (9 <ℕ∞ 11) ≡ ⊤
<ℕ∞-test4 = refl
<ℕ∞-test5 : (λ x → x <ℕ∞ 0) ≡ (λ x → ⊥)
<ℕ∞-test5 = refl

-- NEHÉZ LEHET: Ha az előző jól van megcsinálva, akkor ez triviális.
-- Bizonyítsd be, hogy ∀ n : ℕ-re n <ℕ∞ ∞
n<∞ : ∀ n → n <ℕ∞ ∞
n<∞ = ?