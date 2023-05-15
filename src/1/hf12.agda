module hf12 where

open import lib
open import proofs

Dec : ∀{i} → Set i → Set i
Dec A = A ⊎ ¬ A

_≟⊤_ : (a b : ⊤) → Dec (a ≡ b)
_≟⊤_ = {!   !}

_≟⊥_ : (a b : ⊥) → Dec (a ≡ b)
_≟⊥_ = {!   !}

-----------------------------------------------
-- Bool műveletek
-----------------------------------------------

infixr 9 ¬ᵇ_
infixr 3 _∧_
infixr 2 _∨_
infixr 1 _⊃_
_∧_ _∨_ _⊃_ : Bool → Bool → Bool
¬ᵇ_ : Bool → Bool

true  ∧ x = x
false ∧ _ = false

true  ∨ _ = true
false ∨ x = x

false ⊃ _ = true
true  ⊃ x = x

¬ᵇ false = true
¬ᵇ true  = false

task1 : Dec (∀ x y → (x ⊃ y) ≡ (¬ᵇ x ∨ ¬ᵇ y))
task1 = {!   !}

task2 : ∀ x → x ≢ ¬ᵇ x
task2 = {!   !}

task3 : ∀ x → (x ∧ ¬ᵇ x) ≢ (x ∨ ¬ᵇ x)
task3 = {!   !}

----------------------------------------------
-- Bool függvények injektivitása
----------------------------------------------

¬inj : ∀ a b → ¬ᵇ a ≡ ¬ᵇ b → a ≡ b
¬inj = {!   !}

∧≢ : ∀ a b c → (a ∧ b) ≢ (a ∧ c) → b ≢ c
∧≢ = {!   !}

∧notinjl : ¬ (∀ a b c → (a ∧ b) ≡ (a ∧ c) → b ≡ c)
∧notinjl = {!   !}

∧notinjr : ¬ (∀ a b c → (a ∧ c) ≡ (b ∧ c) → a ≡ b)
∧notinjr = {!   !}

∨notinjl : ¬ (∀ a b c → (a ∨ b) ≡ (a ∨ c) → b ≡ c)
∨notinjl = {!   !}

∨notinjr : ¬ (∀ a b c → (a ∨ c) ≡ (b ∨ c) → a ≡ b)
∨notinjr = {!   !}

⊃notinjl : ¬ (∀ a b c → (a ⊃ b) ≡ (a ⊃ c) → b ≡ c)
⊃notinjl = {!   !}

⊃notinjr : ¬ (∀ a b c → (a ⊃ c) ≡ (b ⊃ c) → a ≡ b)
⊃notinjr = {!   !}

----------------------------------------------
-- Nem egyenlőség természetes számokon
----------------------------------------------

task4 : ∀ n → Σ ℕ (n ≢_)
task4 = {!   !}

task5 : Σ ℕ (λ n → ∀ m → n ≢ suc m)
task5 = {!   !}

task6 : ¬ ((n k : ℕ) → 2 ^ suc n ≡ 3 ^ suc k)
task6 = {!   !}

task7 : (n k : ℕ) → 2 ^ suc n ≢ 3 ^ suc k
task7 = {!   !}

----------------------------------------------
-- Bizonyítások injektivitása
----------------------------------------------

-- Írd fel a × injektivitását kimondó állítást, majd bizonyítsd!
-- f injektív <-> f a = f b -> a = b
-- Ez két paraméter esetén is így van:
-- f a b = f a' b' -> a = a' ÉS b = b'
-- Ez mindkét irányba működik, ezért így is írd fel.
×inj : ∀{i j}{A : Set i}{B : Set j}{a a' : A}{b b' : B} →
  {!   !}
×inj = {!   !}

-- Írd fel a Σ injektivitását kimondó állítást, majd bizonyítsd!
-- Ezt ténylegesen csak szétszedni lehet jól.
-- Összerakáshoz egy külön feladat szükséges (ez a következő lesz).
Σinj : ∀{i j}{A : Set i}{B : A → Set j}{a b : Σ A B} →
  {!   !}
Σinj = {!   !}

-- Egy Σ-ban lévő bizonyítás akkor fog teljesülni,
-- ha az első IS igaz és a második IS igaz.
-- Írd fel az állítást és bizonyítsd.
infixr 4 _,=_
_,=_ : ∀{i j}{A : Set i}{B : A → Set j}{a b : A}{x : B a}{y : B b} →
  {!   !}
_,=_ = {!   !}