{-
Fin (sum F) ↔ Σ (Fin n) (λ i → Fin (F i))

n = 3

F 0 = 3
F 1 = 2
F 2 = 4

Fin (3 + 2 + 4) = Fin 9

(0 , _ : Fin 3) vagy (1 , _ : Fin 2) vagy (2 , _ : Fin 4)

Fin 3 ⊎ (Fin 2 ⊎ Fin 4)
-}

-- matek = programozas

-- klasszikus logika

open import Lib renaming (_∧_ to _∧B_; _∨_ to _∨B_; ¬_ to ¬B_)

module ea08 where

module Tarski where
  allitas : Set
  _∧_   : allitas → allitas → allitas
  _∨_   : allitas → allitas → allitas
  ¬_    : allitas → allitas
  igaz  : allitas
  hamis : allitas
  _⇒_   : allitas → allitas → allitas
  ∀'    : (ℕ → allitas) → allitas
  ∃     : (ℕ → allitas) → allitas

  allitas = Bool  -- Alfred Tarsi
  _∧_ = _∧B_
  _∨_ = _∨B_
  ¬ true = false
  ¬ false = true
  igaz  = true
  hamis = false
  false ⇒ B = true
  true  ⇒ B = B
  -- A ⇒ B = (¬ A) ∨ B

  -- klasszikus szemantika, iteletlogikara (0.rendu logikara) jol mukodik

  -- minden termeszetes szamra igaz valami
  ∀' P = {!P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ ... !} -- soha nem tudjuk meg, ha ez igaz

  ∃ P = {!P 0 ∨ P 1 ∨ P 2 ∨ P 3 ∨ ...!} -- soha nem tudjuk meg, hogyha ez hamis

  -- a Tarski szemantika tul limitalt

-- Heyting, Kolmogorov

allitas : Set₁
_∧_   : allitas → allitas → allitas
_∨_   : allitas → allitas → allitas
¬_    : allitas → allitas
igaz  : allitas
hamis : allitas
_⇒_   : allitas → allitas → allitas
∀'    : (ℕ → allitas) → allitas
∃     : (ℕ → allitas) → allitas

allitas = Set -- Heyting szemantika: az allitas az o bizonyitasainak a halmaza (tipusa)

A ∧ B = A × B
A ∨ B = A ⊎ B
igaz  = ⊤
hamis = ⊥
A ⇒ B = A → B
¬ A   = A ⇒ hamis
∀' P  = (n : ℕ) → P n  -- Stream A = A ^ ℕ = ℕ → A
∃  P  = Σ ℕ P          

-- predikatum / unaris relacio
paros : ℕ → allitas
paros 0 = igaz
paros (suc n) = ¬ paros n

elsoAgdaBizonyitasom : paros 4 -- matematikai allitas
elsoAgdaBizonyitasom = λ input → input λ input' → input' tt

masodikAgdaBizonyitasom : ¬ paros 3
masodikAgdaBizonyitasom = elsoAgdaBizonyitasom

p3 : ∀' (λ n → paros n ⇒ paros (2 + n))
p3 = λ _ a f → f a
-- ℕ → A → (A → B) → B

-- bizonyitas = programozas
-- Bool, ℕ, ℕ → ℕ

_≤_ : ℕ → ℕ → Set
zero  ≤ _     = ⊤
suc _ ≤ zero  = ⊥
suc m ≤ suc n = m ≤ n

p4 : 2 ≤ 5 -- = suc 1 ≤ suc 4 = 1 ≤ 4 = suc zero ≤ suc 3 = zero ≤ 3 = ⊤
p4 = tt

p5 : ¬ (3 ≤ 2)
p5 = λ feltetel → feltetel

p6 : Σ ℕ λ n → n ≤ 0
p6 = 0 , tt

infix 4 _≤_ 

p7 : ¬ Σ ℕ λ n → 1 + n ≤ 0
p7 = λ f → snd f
-- 1 + n ≤ 0 = suc zero + n ≤ zero = suc (zero + n) ≤ zero = suc n ≤ zero = ⊥

-- p8'' : (n : ℕ) → Vec Bool n
-- p8'' zero = []
-- p8'' (suc n) = true ∷ p8'' n

-- A → B → C
-- (n : ℕ) → P n → ⊥
p8' : (n : ℕ) → ¬ (1 + n ≤ n)
p8' zero    = λ x → x
p8' (suc n) = p8' n

-- rekurziv fuggveny ℕ-en = teljes indukcio

--   A × B → C
--   Σ ℕ P → ⊥
p8 : ¬ Σ ℕ λ n → 1 + n ≤ n
p8 = λ f → p8' (fst f) (snd f)

-- teljes indukcio
-- P : ℕ → Set
-- z : P zero
-- s : (n : ℕ) → P n → P (suc n)
--------------------------------
-- ind : (n : ℕ) → P n

-- jovo oran: t.i. az iteℕ-nek altalanositasa

-- kovetkezo ora 0 perccel rovidebb
