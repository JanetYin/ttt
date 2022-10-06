module t1.gy04 where

open import lib

------------------------------------------------------
-- simple finite types
------------------------------------------------------

flip : ℕ × Bool → Bool × ℕ
flip (n , b) = b , n

flipback : Bool × ℕ → ℕ × Bool
flipback (b , n) = n , b

comm× : {A B : Type} → A × B → B × A
comm× (a , b) = (b , a)

comm×back : {A B : Type} → B × A → A × B
comm×back = comm×

b1 b2 : Bool × ⊤
b1 = true , tt
b2 = false , tt
b1≠b2 : b1 ≡ b2 → ⊥
b1≠b2 ()

t1 t2 : ⊤ ⊎ ⊤
t1 = inl tt
t2 = inr tt
t1≠t2 : t1 ≡ t2 → ⊥
t1≠t2 ()

bb1 bb2 bb3 : Bool ⊎ ⊤
bb1 = inl true
bb2 = inl false
bb3 = inr tt
bb1≠bb2 : bb1 ≡ bb2 → ⊥
bb1≠bb2 ()
bb1≠bb3 : bb1 ≡ bb3 → ⊥
bb1≠bb3 ()
bb2≠bb3 : bb2 ≡ bb3 → ⊥
bb2≠bb3 ()

ee : (⊤ → ⊥) ⊎ (⊥ → ⊤)
ee = inr exfalso

d : (⊤ ⊎ (⊤ × ⊥)) × (⊤ ⊎ ⊥)
d = (inl tt) , (inl tt)

from : {A : Type} → A × A → (Bool → A)
from (a , a') b = if b then a else a'
to : {A : Type} → (Bool → A) → A × A
to = λ f → f true , f false
testfromto1 : {A : Type}{a b : A} → fst (to (from (a , b))) ≡ a
testfromto1 = refl
testfromto2 : {A : Type}{a b : A} → snd (to (from (a , b))) ≡ b
testfromto2 = refl
testfromto3 : {A : Type}{a b : A} → from (to (λ x → if x then a else b)) true ≡ a
testfromto3 = refl
testfromto4 : {A : Type}{a b : A} → from (to (λ x → if x then a else b)) false ≡ b
testfromto4 = refl

------------------------------------------------------
-- all algebraic laws systematically
------------------------------------------------------

-- (⊎, ⊥) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc⊎ : {A B C : Type} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C)
assoc⊎ =
  (λ abc → case abc (λ ab → case ab inl λ b → inr (inl b)) λ c → inr (inr c)) ,
  λ abc → case abc (λ a → inl (inl a)) λ ab → case ab (λ b → inl (inr b)) inr

idl⊎ : {A : Type} → ⊥ ⊎ A ↔ A
idl⊎ = (λ na → case na exfalso (λ a → a)) , inr

idr⊎ : {A : Type} → A ⊎ ⊥ ↔ A
idr⊎ = (λ na → case na (λ a → a) exfalso) , inl

comm⊎ : {A B : Type} → A ⊎ B ↔ B ⊎ A
comm⊎ = (λ ab → case ab inr inl) , (λ ba → case ba inr inl)

-- (×, ⊤) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc× : {A B C : Type} → (A × B) × C ↔ A × (B × C)
assoc× = {!!}

idl× : {A : Type} → ⊤ × A ↔ A
idl× = {!!}

idr× : {A : Type} → A × ⊤ ↔ A
idr× = {!!}

-- ⊥ is a null element

null× : {A : Type} → A × ⊥ ↔ ⊥
null× = {!!}

-- distributivity of × and ⊎

dist : {A B C : Type} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
dist = {!!}

-- exponentiation laws

curry : ∀{A B C : Type} → (A × B → C) ↔ (A → B → C)
curry = {!!}

⊎×→ : {A B C D : Type} → ((A ⊎ B) → C) ↔ (A → C) × (B → C)
⊎×→ = {!!}

law^0 : {A : Type} → (⊥ → A) ↔ ⊤
law^0 = {!!}

law^1 : {A : Type} → (⊤ → A) ↔ A
law^1 = {!!}

law1^ : {A : Type} → (A → ⊤) ↔ ⊤
law1^ = {!!}

---------------------------------------------------------
-- random isomorphisms
------------------------------------------------------

iso1 : {A B : Type} → (Bool → (A ⊎ B)) ↔ ((Bool → A) ⊎ Bool × A × B ⊎ (Bool → B))
iso1 = {!!}

iso2 : {A B : Type} → ((A ⊎ B) → ⊥) ↔ ((A → ⊥) × (B → ⊥))
iso2 = {!!}

iso3 : (⊤ ⊎ ⊤ ⊎ ⊤) ↔ Bool ⊎ ⊤
iso3 = {!!}
testiso3 : fst iso3 (inl tt) ≡ fst iso3 (inr (inl tt)) → ⊥
testiso3 ()
testiso3' : fst iso3 (inl tt) ≡ fst iso3 (inr (inr tt)) → ⊥
testiso3' ()
testiso3'' : fst iso3 (inr (inl tt)) ≡ fst iso3 (inr (inr tt)) → ⊥
testiso3'' ()

iso4 : (⊤ → ⊤ ⊎ ⊥ ⊎ ⊤) ↔ (⊤ ⊎ ⊤)
iso4 = {!!} , {!!}
testiso4 : fst iso4 (λ _ → inl tt) ≡ fst iso4 (λ _ → inr (inr tt)) → ⊥
testiso4 ()
testiso4' : snd iso4 (inl tt) tt ≡ snd iso4 (inr tt) tt → ⊥
testiso4' ()
