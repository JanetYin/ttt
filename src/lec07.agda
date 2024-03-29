module lec07 where

open import Lib hiding (prop; _∧_; _∨_; True; False; ¬_)

{- canvas quiz

Fin (2 * 3)  ↔ ((i:Bool) → Fin(if i then 2 else 3))
Fin (2 * 3 * 7)  ↔ ((i:Three) → Fin(if i=0 then 2 else if i=1 then 3 else 7))

Fin (prod F) ↔ ((i:Fin n) → Fin (F i))

Fin (sum F) ↔ Σ (Fin n) (λ i → Fin (F i))

|____________________________________________| Fin (sum F) = Fin(F0+F1+...+F7)
|__|_____|___|_|______|____|_|_______________|
 F0   F1   F2 F3   F4   F5 F6    F7
-}

module classicalLogic where

  prop  : Set
  _∧_   : prop → prop → prop -- ... and ...
  _∨_   : prop → prop → prop -- ... or ...
  _⇒_   : prop → prop → prop -- if ..., then ...
  True  : prop
  False : prop
  ¬_    : prop → prop -- not ...
  _⇔_   : prop → prop → prop -- ... if and only if ...
  prop  = Bool
  true  ∧ a = a
  false ∧ a = false
  true  ∨ a = true
  false ∨ a = a
  True  = true
  False = false
  true  ⇒ false = false
  _ ⇒ _ = true
  ¬ a     = a ⇒ False
  a ⇔ b   = (a ⇒ b) ∧ (b ⇒ a)

  -- ¬ (a ∧ b) = (¬ a) ∨ (¬ b)

  _===_ : ℕ → ℕ → prop
  zero  === zero  = True
  zero  === suc b = False
  suc a === zero  = False
  suc a === suc b = a === b

  -- ∀n. n+0===n
  -- 
  ∀ℕ : (ℕ → prop) → prop
  ∀ℕ as = {!!} -- as 0 ∧ as 1 ∧ as 2 ∧ as 3 ∧ ...

  ∀3 : (Fin 3 → prop) → prop
  ∀3 as = (as fzero ∧ as (fsuc fzero)) ∧ as (fsuc (fsuc fzero))

  peldaAllitas : prop
  peldaAllitas = ∀ℕ λ n → (n + 0) === n

  ∃ℕ : (ℕ → prop) → prop
  ∃ℕ as = {!!} -- as 0 ∨ as 1 ∨ as 2 ∨ as 3 ∨ ....

  -- Tarski

prop  : Set₁
_∧_   : prop → prop → prop
_∨_   : prop → prop → prop
_⇒_   : prop → prop → prop
True  : prop
False : prop
¬_    : prop → prop
_⇔_   : prop → prop → prop
-- BHK: Brouwer-Heyting-Kolmogorov
prop  = Set
a ⇒ b = a → b
a ∧ b = a × b         --   (n<20) ∧ (n>10) = n<20 × n>10
a ∨ b = a ⊎ b
True  = ⊤
False = ⊥
¬ a     = a ⇒ False
a ⇔ b   = (a ⇒ b) ∧ (b ⇒ a)

∀ℕ : (ℕ → prop) → prop
∀ℕ as = (n : ℕ) → as n -- as 0 × as 1 × as 2 × as 3 × ...

∃ℕ  :  (ℕ → prop) → prop
∃ℕ as = Σ ℕ as

-- BHK interpretation = propositions as types = Curry-Howard izomorfizmus

-- proposition = Set

-- Vladimir Voevodsky: proposition = Σ Set λ A → (a b : A) → a ≡ b
-- homotopy type theory

-- "seemingly impossible functional programs" ((ℕ → Bool) → Bool)

-- next class: examples for propositions
