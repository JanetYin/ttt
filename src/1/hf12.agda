module hf12 where

open import lib
open import proofs

--------------------------------
-- diszjunktság maradék feladat
--------------------------------

-- Próbáljátok ki nyugodtan, hogy ezek
-- működnek mintaillesztéssel,
-- de működnek subst-tal is!

-- Subst-nál ne feledjétek, hogy a konstruktorok
-- csak az érdekesek, az egyikre ⊤-ot ad vissza P,
-- másikra ⊥-ot, akkor megy minden egyszerűen.

n≠sucn : ∀ n → ¬ (n ≡ suc n)
n≠sucn = {!!}

-- Lehet indukciót használni n-en, és oda kell subst,
-- hogy bizonyítsuk, hogy 0 ≢ 1
n≠sucn' : ∀ n → ¬ (n ≡ suc n)
n≠sucn' n = {!!}

leaf≠node : ∀{f} → ¬ (Tree.leaf ≡ node f)
leaf≠node = {!!}

leaf≠nodeSubst : ∀{f} → ¬ (Tree.leaf ≡ node f)
leaf≠nodeSubst = {!!}

leaf≠node' : ∀{x y} → ¬ (BinTree.leaf ≡ node x y)
leaf≠node' = {!!}

leaf≠nodeSubst' : ∀{x y} → ¬ (BinTree.leaf ≡ node x y)
leaf≠nodeSubst' = {!!}

nil≠cons : ∀{A}{x : A}{xs} → ¬ ([] ≡ x ∷ xs)
nil≠cons = {!!}

nil≠cons' : ∀{A}{x : A}{xs} → ¬ ([] ≡ x ∷ xs)
nil≠cons' = {!!}

-----------------------------
-- Eldönthetőség
-----------------------------

Dec : ∀{i} → Set i → Set i
Dec A = A ⊎ ¬ A

_≟⊤_ : (a b : ⊤) → Dec (a ≡ b)
_≟⊤_ = {!   !}

_≟⊥_ : (a b : ⊥) → Dec (a ≡ b)
_≟⊥_ = {!   !}

_≟Bool_ : (b b' : Bool) → Dec (b ≡ b')
_≟Bool_ = {!!}

_≟ℕ_ : (n n' : ℕ) → Dec (n ≡ n')
_≟ℕ_ = {!!}

_≟BinTree_ : (t t' : BinTree) → Dec (t ≡ t')
_≟BinTree_ = {!   !}

_≟List_ : {A : Set} → (xs ys : List A) → {f : (x y : A) → Dec (x ≡ y)} → Dec (xs ≡ ys)
_≟List_ = {!   !}

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

¬¬involutive : ∀ a → ¬ᵇ ¬ᵇ a ≡ a
¬¬involutive = {!   !}

----------------------------------------------
-- ℕ függvények injektivitása
----------------------------------------------

+injl : {n m k : ℕ} → n + m ≡ n + k → m ≡ k
+injl = {!   !}

+injr : {n m k : ℕ} → n + m ≡ k + m → n ≡ k
+injr = {!   !}

*injr : {n m k : ℕ} → n * suc m ≡ k * suc m → n ≡ k
*injr = {!   !}

*injl : {n m k : ℕ} → suc n * m ≡ suc n * k → m ≡ k
*injl = {!   !}

----------------------------------------------
-- Nem egyenlőség természetes számokon
----------------------------------------------

task4 : ¬ ((n : ℕ) → n ≡ 3)
task4 = {!   !}

task5 : {n : ℕ} → n ≡ 3 → n ≢ 10
task5 = {!   !}

task6 : ∀ n → Σ ℕ (n ≢_)
task6 = {!   !}

task7 : Σ ℕ (λ n → ∀ m → n ≢ suc m)
task7 = {!   !}

task8 : ¬ ((n k : ℕ) → 2 ^ suc n ≡ 3 ^ suc k)
task8 = {!   !}

task9 : (n k : ℕ) → 2 ^ suc n ≢ 3 ^ suc k
task9 = {!   !}

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

------------------------------
-- ≢ tulajdonságok
------------------------------

≢notTrans : ∀{i} → ¬ ({A : Set i}{a b c : A} → a ≢ b → b ≢ c → a ≢ c)
≢notTrans = {!   !}

≢notReflexive : ∀{i}{A : Set i}{a : A} → ¬ (a ≢ a)
≢notReflexive = {!   !}

------------------------------
-- ≢ típusokon
------------------------------

-- Trükkös feladat, jó ötlet kell hozzá!
-- Arra kell gondolni, hogy ha két típus egyenlő, akkor
-- ebből milyen tulajdonságokat kapunk.
task10 : ⊤ ≢ (⊤ ⊎ ⊤)
task10 eq = {!   !}