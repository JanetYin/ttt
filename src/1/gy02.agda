open import lib

------------------------------------------------------
-- simple finite types
------------------------------------------------------
{-
data Bool : Set where
  false : Bool
  true  : Bool
-}

the : (A : Set) → A → A
the A x = x

_! : ℕ → ℕ
n ! = {!   !}

flip : ℕ × Bool → Bool × ℕ
flip (x , y) = y , x

flipback : Bool × ℕ → ℕ × Bool
flipback = λ {(y , x) → x , y}

comm× : {A B : Set} → A × B → B × A
comm× (a , b) = b , a

comm×back : {A B : Set} → B × A → A × B
comm×back = comm×

-- \x = ×
-- \top = ⊤
b1 b2 : Bool × ⊤
b1 = true , tt
b2 = false , tt
b1≠b2 : b1 ≢ b2
b1≠b2 ()

-- \u+ = ⊎
t1 t2 : ⊤ ⊎ ⊤
t1 = inr tt
t2 = inl tt
t1≠t2 : t1 ≢ t2
t1≠t2 ()

bb1 bb2 bb3 : Bool ⊎ ⊤
bb1 = {!!}
bb2 = {!!}
bb3 = {!!}
bb1≠bb2 : bb1 ≢ bb2
bb1≠bb2 = {!!}
bb1≠bb3 : bb1 ≢ bb3
bb1≠bb3 = {!!}
bb2≠bb3 : bb2 ≢ bb3
bb2≠bb3 = {!!}

-- \bot = ⊥
ee : (⊤ → ⊥) ⊎ (⊥ → ⊤)
ee = inr λ x → tt

d : (⊤ ⊎ (⊤ × ⊥)) × (⊤ ⊎ ⊥)
d = inl tt , inl tt

from : {A : Set} → A × A → (Bool → A)
from (x , y) false = x
from (x , y) true = y

to : {A : Set} → (Bool → A) → A × A
to f = (f false) , (f true)

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

-- (⊎, ⊥) form a commutative monoid (kommutativ egysegelemes felcsoport)

-- \<-> = ↔
assoc⊎ : {A B C : Set} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C)
assoc⊎ = to' , from' where
  to' : {A B C : Set} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
  to' (inl (inl x)) = inl x
  to' (inl (inr x)) = inr (inl x)
  to' (inr x) = inr (inr x)

  from' : {A B C : Set} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
  from' (inl x) = inl (inl x)
  from' (inr (inl x)) = inl (inr x)
  from' (inr (inr x)) = inr x

idl⊎ : {A : Set} → ⊥ ⊎ A ↔ A
idl⊎ = {!!}

idr⊎ : {A : Set} → A ⊎ ⊥ ↔ A
idr⊎ = {!!}

comm⊎ : {A B : Set} → A ⊎ B ↔ B ⊎ A
comm⊎ = {!!}

-- (×, ⊤) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc× : {A B C : Set} → (A × B) × C ↔ A × (B × C)
assoc× = {!!}

idl× : {A : Set} → ⊤ × A ↔ A
idl× = {!!}

idr× : {A : Set} → A × ⊤ ↔ A
idr× = {!!}

-- ⊥ is a null element

null× : {A : Set} → A × ⊥ ↔ ⊥
null× = {!!}

-- distributivity of × and ⊎

dist : {A B C : Set} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
dist = {!!}

-- exponentiation laws

curry : ∀{A B C : Set} → (A × B → C) ↔ (A → B → C)
curry = {!!}

⊎×→ : {A B C D : Set} → ((A ⊎ B) → C) ↔ (A → C) × (B → C)
⊎×→ = {!!}

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

iso3 : (⊤ ⊎ ⊤ ⊎ ⊤) ↔ Bool ⊎ ⊤
iso3 = {!!}
testiso3 : fst iso3 (inl tt) ≢ fst iso3 (inr (inl tt))
testiso3 ()
testiso3' : fst iso3 (inl tt) ≢ fst iso3 (inr (inr tt))
testiso3' ()
testiso3'' : fst iso3 (inr (inl tt)) ≢ fst iso3 (inr (inr tt))
testiso3'' ()

iso4 : (⊤ → ⊤ ⊎ ⊥ ⊎ ⊤) ↔ (⊤ ⊎ ⊤)
iso4 = {!!}
testiso4 : fst iso4 (λ _ → inl tt) ≢ fst iso4 (λ _ → inr (inr tt))
testiso4 ()
testiso4' : snd iso4 (inl tt) tt ≢ snd iso4 (inr tt) tt
testiso4' ()
