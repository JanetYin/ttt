open import lib

-- about _×_ (\x) and _⊎_ (\u+)

rec : ℕ × Bool
-- fst rec = 5
-- snd rec = true
rec = 5 , true

-- 5 , 4 != 4 , 5

un1 un2 : ℕ ⊎ Bool
un1 = inl 5
un2 = inr true

un3 : ℕ ⊎ ℕ
un3 = inr 5

-- inl 5 =? inr 5

-- Maybe is actually ℕ ⊎ ⊤

-- NOTE: until here (and case in lib)

------------------------------------------------------
-- simple finite types
------------------------------------------------------

-- look at the definition with M-.
-- pattern matching: C-c C-c
flip : ℕ × Bool → Bool × ℕ
flip = {!!}

flipback : Bool × ℕ → ℕ × Bool
flipback = {!!}

-- in general:
comm× : {A B : Set} → A × B → B × A
comm× = {!!}
-- basically, this is the only way it can be defined

comm×back : {A B : Set} → B × A → A × B
comm×back = comm×

b1 b2 : Bool × ⊤
b1 = {!!}
b2 = {!!}
b1≠b2 : b1 ≡ b2 → ⊥  --what is this?
b1≠b2 ()

t1 t2 : ⊤ ⊎ ⊤
t1 = {!!}
t2 = {!!}
t1≠t2 : t1 ≡ t2 → ⊥
t1≠t2 ()

-- why 3?
bb1 bb2 bb3 : Bool ⊎ ⊤
bb1 = {!!}
bb2 = {!!}
bb3 = {!!}
bb1≠bb2 : bb1 ≡ bb2 → ⊥
bb1≠bb2 ()
bb1≠bb3 : bb1 ≡ bb3 → ⊥
bb1≠bb3 ()
bb2≠bb3 : bb2 ≡ bb3 → ⊥
bb2≠bb3 ()

ee : (⊤ → ⊥) ⊎ (⊥ → ⊤)
ee = {!!}

-- how many different elements does this type have?
d : (⊤ ⊎ (⊤ × ⊥)) × (⊤ ⊎ ⊥)
d = {!!}

from : {A : Set} → A × A → (Bool → A)
from = {!!}
to : {A : Set} → (Bool → A) → A × A
to = {!!}
bij : {A : Set} → A × A ↔ (Bool → A)
bij = from , to
-- ez igazából annak tesztelése, hogy ez bijekció
-- és miért kell ezt tesztelni? mert amúgy tudnál ⊤ ↔ Bool-t is csinálni
testfromto1 : {A : Set}{a b : A} → fst (to (from (a , b))) ≡ a
testfromto1 = refl
testfromto2 : {A : Set}{a b : A} → snd (to (from (a , b))) ≡ b
testfromto2 = refl
testfromto3 : {A : Set}{a b : A} → from (to (λ x → if x then a else b)) true ≡ a
testfromto3 = refl
testfromto4 : {A : Set}{a b : A} → from (to (λ x → if x then a else b)) false ≡ b
testfromto4 = refl

------------------------------------------------------
-- all algebraic laws systematically
------------------------------------------------------

-- Curry–Howard correspondence

-- (⊎, ⊥) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc⊎ : {A B C : Set} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C)
assoc⊎ = {!!}

idl⊎ : {A : Set} → ⊥ ⊎ A ↔ A
idl⊎ = {!!}

-- homework
idr⊎ : {A : Set} → A ⊎ ⊥ ↔ A
idr⊎ = {!!}

comm⊎ : {A B : Set} → A ⊎ B ↔ B ⊎ A
comm⊎ = {!!}

-- (×, ⊤) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc× : {A B C : Set} → (A × B) × C ↔ A × (B × C)
assoc× = {!!}

idl× : {A : Set} → ⊤ × A ↔ A
idl× = {!!}

-- homework
idr× : {A : Set} → A × ⊤ ↔ A
idr× = {!!}

-- ⊥ is a null element

nullr× : {A : Set} → A × ⊥ ↔ ⊥
nullr× = {!!}

-- distributivity of × and ⊎

dist : {A B C : Set} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
dist = {!!}

-- exponentiation laws

curry : ∀{A B C : Set} → (A × B → C) ↔ (A → B → C)
curry = {!!}
-- think of it another way: C^(A×B)=(C^B)^A

-- homework
⊎×→ : {A B C D : Set} → ((A ⊎ B) → C) ↔ (A → C) × (B → C)
⊎×→ = {!!}
-- C^(A+B)=(C^A)×(C^B)

law^0 : {A : Set} → (⊥ → A) ↔ ⊤
law^0 = {!!}

law^1 : {A : Set} → (⊤ → A) ↔ A
law^1 = {!!}

law1^ : {A : Set} → (A → ⊤) ↔ ⊤
law1^ = {!!}

---------------------------------------------------------
-- random isomorphisms
------------------------------------------------------

iso1 : {A B : Set} → (Bool → (A ⊎ B)) ↔ ((Bool → A) ⊎ Bool × A × B ⊎ (Bool → B))
iso1 = {!!}

iso2 : {A B : Set} → ((A ⊎ B) → ⊥) ↔ ((A → ⊥) × (B → ⊥))
iso2 = {!!}

-- here make sure that it is a bijection
iso3 : (⊤ ⊎ ⊤ ⊎ ⊤) ↔ Bool ⊎ ⊤
iso3 = {!!}
testiso3 : fst iso3 (inl tt) ≡ fst iso3 (inr (inl tt)) → ⊥
testiso3 ()
testiso3' : fst iso3 (inl tt) ≡ fst iso3 (inr (inr tt)) → ⊥
testiso3' ()
testiso3'' : fst iso3 (inr (inl tt)) ≡ fst iso3 (inr (inr tt)) → ⊥
testiso3'' ()

-- here too
iso4 : (⊤ → ⊤ ⊎ ⊥ ⊎ ⊤) ↔ (⊤ ⊎ ⊤)
iso4 = {!!} , {!!}
testiso4 : fst iso4 (λ _ → inl tt) ≡ fst iso4 (λ _ → inr (inr tt)) → ⊥
testiso4 ()
testiso4' : snd iso4 (inl tt) tt ≡ snd iso4 (inr tt) tt → ⊥
testiso4' ()
