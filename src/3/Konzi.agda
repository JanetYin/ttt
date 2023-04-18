open import Agda.Builtin.Nat renaming (Nat to ℕ)


data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)

-- dimaton voltak a ciklikus csoportok / gyűrűk
-- ℤ\5 <- olyan gyűrű ami 5-ig tartalmazza az elemeket

-- Fin n az maximum n-t tárolhat el


f1 : Fin 1
f1 = zero

f2 : Fin 1
f2 = suc {!!} -- Fin 0 kéne
-- Fin 0 ∄
--
-- Fin k esetén k vagy kevesebb suc kell
--

----------------------------------------------------

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma

--record Σ {ℓ κ}(A : Set ℓ)(P : A → Set κ) : Set (ℓ ⊔ κ) where
--  constructor _,_
--  field
--    fst : A
--    snd : P fst

_×_ : ∀{ℓ κ} → Set ℓ → Set κ → Set (ℓ ⊔ κ)
A × B = Σ A λ _ → B

if_then_else_ : ∀{ℓ}{A : Set ℓ} → Bool → A → A → A
if true then a else b = a
if false then a else b = b

_↔_ : ∀{ℓ κ} → Set ℓ → Set κ → Set (ℓ ⊔ κ)
A ↔ B = (A → B) × (B → A)

data _⊎_ {ℓ}{κ}(A : Set ℓ)(B : Set κ) : Set (ℓ ⊔ κ) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

case : ∀ {i j k}{A : Set i}{B : Set j}{C : Set k}
         (t : A ⊎ B)(u : A → C)(v : B → C) → C
case (inl t) u v = u t
case (inr t) u v = v t

-- Bizonyítsd az alábbi bijekciót!

Σ↔↔ : {A B C : Set} → Σ (A × C → B) (λ _ → (B → C × A)) ↔ ((A × C) ↔ B)
fst (fst Σ↔↔ (A×C→B , B→C×A)) = A×C→B
snd (fst Σ↔↔ (A×C→B , B→C×A)) b = (snd (B→C×A b)) , (fst (B→C×A b))
fst (snd Σ↔↔ (A×C→B , B→A×C)) = A×C→B
snd (snd Σ↔↔ (A×C→B , B→A×C)) b = (snd (B→A×C b)) , (fst (B→A×C b))

-- Legyen az a logikai igaz
-- Hogy egy típusnak van eleme
-- Legyen az a logikai hamis
-- Hogy nincs eleme

data ⊥ : Set where

-- Az a következménye
-- {A : Set} <- tetszőleges logikai ítéletváltozó
-- logikai ÉS / konjukció -> A ∧ B == A × B
-- logikai VAGY / diszjunkció -> A v B == A ⊎ B
-- logikai implikáció -> A ⊃ B = A → B !! kis side effect
-- logikai negáció -> ¬ A = "ez az állítás hamis" = "ennek a típusnak nincs eleme" = A → ⊥

¬_ : ∀{ℓ} → Set ℓ → Set ℓ
¬ A = A → ⊥

-- exfalso : ⊥ → A
exfalso : ∀{ℓ}{A : Set ℓ} → ⊥ → A
exfalso ()

a⊃a : {A : Set} → A → A
a⊃a A = A

anything : {X Y : Set} → ¬ X → X → Y -- !! ¬ X ≣ X → ⊥
anything ¬X X = exfalso (¬X X)

-- gyengítés
x→¬¬x : {X : Set} → X → ¬ ¬ X -- X → (¬ X) → ⊥
x→¬¬x x ¬x = ¬x x

-- erősítés
¬¬x→x : {X : Set} → ¬ ¬ X → X
¬¬x→x ¬¬x = exfalso (¬¬x (λ x → {!!})) -- exfalso!!

-- Ezt agdába nem lehet bebizonyítani
-- "konstruktív logika"
-- vs
-- logikán "klasszikus logika"


-------------

Dec : ∀{ℓ} → Set ℓ → Set ℓ
Dec A = A ⊎ (¬ A)

dec1 : {A : Set} → Dec (A → A)
dec1 = inl (λ z → z)

dec2 : {A : Set} → Dec (A → ¬ A)
dec2 = inr (λ x → ?)
