module ea07 where

open import lib hiding (¬_; _==_)

{-
Canvas


((b : Bool) → C b)  ↔ (C true × C false) = A × B  ↔ Σ A (λ _ → B)

A ⊎ B ↮ A × B ↔ (b : Bool) → C b	

Σ Bool C ↔ A ⊎ B ↮ A × B ↔ (b : Bool) → C b

A ⊎ B ↮ A × B ↔ Σ A (λ _ → B)

Bool ⊎ Bool ↔ Bool × Bool

λ A B → A × B = λ A → (λ B → A × B)
Set → Set → Set =
(A : Set)(B : Set) → Set
(A : Set i)(B : Set j) → Set (i ⊔ j)

(A : Set _i_12) (B : Set (_j_13 (A = A))) → Set (_i_12 Agda.Primitive.⊔ _j_13 (A = A))

(b : Bool) → if b then Fin 2 else Fin 3   ↔   Fin 2  × Fin 3
(b : Bool) → C b                          ↔   C true × C false


-}


-- ez az ora 11 perccel rovidebb

-- logika

-- prop = Bool

module classical where
  prop  : Set
  _∧_   : prop → prop → prop
  _∨_   : prop → prop → prop
  ¬_    : prop → prop
  _⊃_   : prop → prop → prop
  True  : prop
  False : prop

  prop = Bool
  true  ∧ b = b
  _     ∧ _ = false
  false ∨ b = b 
  _     ∨ _ = true
  ¬ true    = false
  ¬ false   = true
  false ⊃ b = true
  true  ⊃ b = b
  True      = true
  False     = false
  _==_ : prop → prop → prop
  true  == true  = true
  false == false = true
  _     == _     = false

  -- klasszikus logika, kizart harmadik elve (law of excluded middle, lem)

  lem : (a : prop) → prop
  lem a = (a ∨ (¬ a))

  -- De Morgan

  -- (¬ a) ∨ (¬ b) == ¬ (a ∧ b)
  -- (¬ a) ∧ (¬ b) == ¬ (a ∨ b)

  -- ∀, ∃    ∀ n . (Even(n) ⊃ Odd(n+3))

  ∀' : (ℕ → prop) → prop
  ∀' A = {!A 0 ∧ A 1 ∧ A 2 ∧ A 3 ∧ ...!}

  -- ∃ n . n+3 = 10
  -- ∃ n . n+3 = n+2
  ∃ : (ℕ → prop) → prop   
  ∃ A = {!A 0 ∨ A 1 ∨ A 2 ∨ A 3 ∨ ...!}

-- Tarski-fele klasszikus logika

-- Heyting, Brouwer-Heyting-Kolmogorov interpretation, Curry-Howard correspondance,
-- propositions as types

-- az allitas nem mas, mint a sajat bizonyitasainak a halmaza

prop  : Set₁
_∧_   : prop → prop → prop
_∨_   : prop → prop → prop
¬_    : prop → prop
_⊃_   : prop → prop → prop
True  : prop
False : prop
prop  = Set
A ∧ B = A × B
A ∨ B = A ⊎ B
A ⊃ B = A → B
True  = ⊤
False = ⊥
¬ A   = A ⊃ False

-- intuicionista logika, konstruktiv logika

∀' : (ℕ → prop) → prop
∀' A = (i : ℕ) → A i

-- ∃ n . n+3 = 10
-- ∃ n . n+3 = n+2
∃ : (ℕ → prop) → prop   
∃ A = Σ ℕ A

-- predikatum, unaris relacio

Even : ℕ → Set
Even zero = ⊤
Even (suc zero) = ⊥
Even (suc (suc n)) = Even n

elsoAgdaBizonyitasom : Even 14
elsoAgdaBizonyitasom = tt

nemAmasodikAgdaBizonyitasom : ¬ Even 14 -- = ¬ ⊤ = ⊤ ⊃ False = ⊤ → ⊥
nemAmasodikAgdaBizonyitasom = {!ilyet nem tudok irni!}

masodikAgdaBizonyitasom : ¬ Even 13
masodikAgdaBizonyitasom = λ x → x

_≤_ : ℕ → ℕ → Set
zero  ≤ n     = ⊤
suc m ≤ zero  = ⊥
suc m ≤ suc n = m ≤ n
-- Σ ℕ λ z → m + z == n

3≤4 : 3 ≤ 4 -- Haskell konvencio, Simonyi convention, Hungarian convention
3≤4 = tt

vanszam : Σ ℕ λ x → (x + 3) ≤ 10
vanszam = 0 , tt

lem : (A : Set) → A ⊎ (A → ⊥)
lem A = {!!}

-- ¬lem : ¬ ((A : Set) → A ⊎ (A → ⊥)) <- nem lehet belatni Agdaban
-- lem  : (A : Set) → A ⊎ (A → ⊥)     <- nem lehet belatni Agdaban

-- ¬¬lem : ¬ (¬ ((A : Set) → A ⊎ (A → ⊥)))
-- ¬¬lem = ?



-- predikatumok, Even, _≤_

-- Andrej Bauer: 5 steps in accepting constructive mathematics

-- kovetkezo eloadas 11 perccel robidebb
