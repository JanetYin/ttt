open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Agda.Primitive

-- ez csak libetlenkedés
if_then_else_ : ∀ {i}{A : Set i} → Bool → A → A → A
if true then a else _ = a
if false then _ else a = a

data ⊥ : Set where

data List {i} (A : Set i) : Set i where
  [] : List A
  _∷_ : A → List A → List A

data Vec {i} (A : Set i) : ℕ → Set i where
  [] : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

---------------------------------------------

-- Írj függvényt, ami Finből ℕ-ba konvertál! A típusszignatúrát is te add meg!
toℕ : ∀ {n : ℕ} → Fin n → ℕ
toℕ = {!!}

-- Írj függvényt, ami Fin n-ből Fin (suc n)-be konvertál úgy, hogy az értéket meghagyja!
-- Pl. a Fin 5-beli suc (suc zero)-ból legyen a Fin 6-beli suc (suc zero).
inject₁ : {n : ℕ} → Fin n → Fin (suc n)
inject₁ = {!!}

-- ezzel tesztelhetsz
-- test-inject₁ : ∀ {n : ℕ}(k : Fin n) → toℕ k ≡ toℕ (inject₁ k)
-- test-inject₁ = refl

-- Írj függvényt, ami duplikálja egy lista elemeit!
-- Pl. duplicate (1 ∷ (2 ∶∶ [])) ≡ 1 ∷ (1 ∷ (2 ∷ (2 ∷ []))).
-- A típusszignatúrát is te add meg (lehetőleg úgy, hogy ne csak sima Setre működjön a függvény).
duplicate : {!!}
duplicate = {!!}
-- Ha van kedved, gondolkodhatsz rajta, hogy vektorra miért nem működik. Persze ehhez próbáld meg megírni;)

-- Írd be egy vektorba Fin n összes elemét, növekvő sorrendben! A típusszignatúrát is te add meg!
-- Segítség: használj korábbi függvényt (másold be ide).
tabulate : ∀ {i} {A : Set i} {n : ℕ} → (Fin n → A) → Vec A n
tabulate {n = zero} f = []
tabulate {n = suc n} f = f zero ∷ tabulate λ k → f (suc k)

{-
f zero = zero
f (suc zero) = suc zero
f (suc (suc zero)) = suc (suc zero)
-}

-- itt ízlés kérdése, hogy n rejtett-e vagy sem
allFins : {n : ℕ} → Vec (Fin n) n
allFins = tabulate λ x → x

example : Vec (Fin 6) 6
example = allFins {6}

-- Írj függvényt, ami egy vektor elemeit megfordítja!
-- Segítség: használj segédfüggvényt, aminek két vektorparamétere van. Az egyikből pakoljunk át a másikba.
reverse : ∀ {i} {A : Set i} {n : ℕ} → Vec A n → Vec A n
reverse = {!!}
