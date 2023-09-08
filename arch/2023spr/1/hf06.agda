module hf06 where

open import lib
open import Agda.Primitive

infixr 5 _∷_
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

map : {A B : Set}{n : ℕ} → (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_++_ : {A : Set}{m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

elimVecᵣ : {A : Set}{n : ℕ}(B : ℕ → Set) → ({n : ℕ} → A → B n → B (suc n)) → B 0 → Vec A n → B n
elimVecᵣ B f acc [] = acc
elimVecᵣ B f acc (x ∷ xs) = f x (elimVecᵣ B f acc xs)

elimVecₗ : {A : Set}{n : ℕ}(B : ℕ → Set) → ({n : ℕ} → B n → A → B (suc n)) → B 0 → Vec A n → B n
elimVecₗ B f acc [] = acc
elimVecₗ B f acc (x ∷ xs) = elimVecₗ (λ z → B (suc z)) f (f acc x) xs

--------------------------------------------------------

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
infix 4 _≤_
_≤_ : ℕ → ℕ → Set
_≤_ = {!   !}

≤-test1 : (λ x → 0 ≤ x) ≡ (λ x → ⊤)
≤-test1 = refl

≤-test2 : 3 ≤ 10
≤-test2 = tt

≤-test3 : ¬ (10 ≤ 3)
≤-test3 ()

infix 4 _≥_
_≥_ : ℕ → ℕ → Set
_≥_ = {!   !}

≥-test1 : (λ x → x ≥ 0) ≡ (λ x → ⊤)
≥-test1 = refl

≥-test2 : 30 ≥ 10
≥-test2 = tt

≥-test3 : ¬ (10 ≥ 30)
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
-}
min : (x : ℕ) → (y : ℕ) → Σ ℕ (λ n → if x < y then n ≡ℕ x else (n ≡ℕ y))
min = {!   !}

min-test1 : fst (min 3 6) ≡ 3
min-test1 = refl

min-test2 : fst (min 6 4) ≡ 4
min-test2 = refl

min-test3 : fst (min 5 5) ≡ 5
min-test3 = refl

max : (x : ℕ) → (y : ℕ) → Σ ℕ (λ n → if y < x then n ≡ℕ x else (n ≡ℕ y))
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
takeWhile : {A : Set}{n : ℕ} → (A → Bool) → Vec A n → Σ ℕ (Vec A)
takeWhile = {!   !}

takeWhile-test1 : takeWhile even (2 ∷ 4 ∷ 0 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (3 , 2 ∷ 4 ∷ 0 ∷ [])
takeWhile-test1 = refl

takeWhile-test2 : takeWhile even (1 ∷ 2 ∷ 3 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (0 , [])
takeWhile-test2 = refl

takeWhile-test3 : takeWhile (0 <_) (1 ∷ 2 ∷ 3 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (6 , 1 ∷ 2 ∷ 3 ∷ 3 ∷ 4 ∷ 5 ∷ [])
takeWhile-test3 = refl

takeWhile-test4 : takeWhile (0 <_) (0 ∷ 1 ∷ 2 ∷ 4 ∷ 5 ∷ []) ≡ (0 , [])
takeWhile-test4 = refl

-- NEHÉZ FELADAT
{-
Egészítsd ki a takeWhile definícióját egy bizonyítással, amely azt mondja,
hogy az eredmény elemszáma legfeljebb n.
-}

takeWhile' : {A : Set}{n : ℕ} → (A → Bool) → Vec A n → Σ ℕ (λ x → Vec A x × x ≤ n)
takeWhile' = {!   !}

takeWhile'-test1 : takeWhile' even (2 ∷ 4 ∷ 0 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (3 , 2 ∷ 4 ∷ 0 ∷ [] , tt)
takeWhile'-test1 = refl

takeWhile'-test2 : takeWhile' even (1 ∷ 2 ∷ 3 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (0 , [] , tt)
takeWhile'-test2 = refl

takeWhile'-test3 : takeWhile' (0 <_) (1 ∷ 2 ∷ 3 ∷ 3 ∷ 4 ∷ 5 ∷ []) ≡ (6 , 1 ∷ 2 ∷ 3 ∷ 3 ∷ 4 ∷ 5 ∷ [] , tt)
takeWhile'-test3 = refl

takeWhile'-test4 : takeWhile' (0 <_) (0 ∷ 1 ∷ 2 ∷ 4 ∷ 5 ∷ []) ≡ (0 , [] , tt)
takeWhile'-test4 = refl


-- Csak hosszabb, de nem igényel a feladat semmi különlegeset.
{-
Definiáld a span függvényt, amely egy vektort két részre bont azon a ponton, ahol
egy adott tulajdonság már nem teljesül.
-}
span : {A : Set}{n : ℕ} → (p : A → Bool) → Vec A n → Σ ℕ (λ x → Σ ℕ (λ y → Vec A x × Vec A y × x + y ≡ℕ n))
span = {!   !}

span-test1 : span even (2 ∷ 4 ∷ 1 ∷ []) ≡ (2 , 1 , 2 ∷ 4 ∷ [] , 1 ∷ [] , tt)
span-test1 = refl

span-test2 : span (_< 3) (2 ∷ 4 ∷ 1 ∷ []) ≡ (1 , 2 , 2 ∷ [] , 4 ∷ 1 ∷ [] , tt)
span-test2 = refl

span-test3 : span (λ _ → false) (2 ∷ 4 ∷ 1 ∷ []) ≡ (0 , 3 , [] , 2 ∷ 4 ∷ 1 ∷ [] , tt)
span-test3 = refl

span-test4 : span (λ _ → true) (2 ∷ 4 ∷ 1 ∷ []) ≡ (3 , 0 , 2 ∷ 4 ∷ 1 ∷ [] , [] , tt)
span-test4 = refl