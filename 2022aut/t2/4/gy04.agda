open import lib

------------------------------------------------------
-- simple finite types
------------------------------------------------------

flip : ℕ × Bool → Bool × ℕ
flip (n , b) = b , n

flipback : Bool × ℕ → ℕ × Bool
flipback (b , n) = n , b

comm× : {A B : Set} → A × B → B × A
comm× (a , b) = b , a

comm×back : {A B : Set} → B × A → A × B
comm×back = comm×

--equality:  \equiv or \==
1issuczero : 1 ≡ suc zero
1issuczero = refl

1iszero : 1 ≡ zero
1iszero = {!!}      -- this will never have an element

b1 b2 : Bool × ⊤    --2 × 1 = 2 elements
b1 = true , tt
b2 = false , tt

--that's an interesting one:
--Agda can automatically deduce they're not equal
b1≠b2 : b1 ≡ b2 → ⊥    -- same as (b1 ≡ b2) → ⊥
b1≠b2 ()

t1 t2 : ⊤ ⊎ ⊤
t1 = inl tt
t2 = inr tt
t1≠t2 : t1 ≡ t2 → ⊥
t1≠t2 ()

bb1 bb2 bb3 : Bool ⊎ ⊤    -- 2 + 1 = 3
bb1 = inl false
bb2 = inl true
bb3 = inr tt
bb1≠bb2 : bb1 ≡ bb2 → ⊥
bb1≠bb2 ()
bb1≠bb3 : bb1 ≡ bb3 → ⊥
bb1≠bb3 ()
bb2≠bb3 : bb2 ≡ bb3 → ⊥
bb2≠bb3 ()

--which one exists?
ee : (⊤ → ⊥) ⊎ (⊥ → ⊤)
ee = inr (λ x → tt)

ee2 : {A : Set} → (⊤ → ⊥) ⊎ (⊥ → A)
ee2 = inr exfalso

d : (⊤ ⊎ (⊤ × ⊥)) × (⊤ ⊎ ⊥)  --(1 + (1 * 0)) * (1 + 0)
d = inl tt , inl tt

--NOTE: we were here

--bijection between (Bool → A) functions and A × A constructs
from : {A : Set} → A × A → (Bool → A)
from = {!!}
to : {A : Set} → (Bool → A) → A × A
to = λ f → f true , f false
testfromto1 : {A : Set}{a b : A} → fst (to (from (a , b))) ≡ a
testfromto1 = refl
testfromto2 : {A : Set}{a b : A} → snd (to (from (a , b))) ≡ b
testfromto2 = refl
testfromto3 : {A : Set}{a b : A} → from (to (λ x → if x then a else b)) true ≡ a
testfromto3 = refl
testfromto4 : {A : Set}{a b : A} → from (to (λ x → if x then a else b)) false ≡ b
testfromto4 = refl

-- Curry–Howard?

------------------------------------------------------
-- all algebraic laws systematically
------------------------------------------------------

-- (⊎, ⊥) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc⊎ : {A B C : Set} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C)
assoc⊎ = {!!}

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
