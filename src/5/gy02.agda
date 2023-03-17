open import lib

------------------------------------------------------
-- simple finite types
------------------------------------------------------

flip : ℕ × Bool → Bool × ℕ
flip (fst₁ , snd₁) = snd₁ , fst₁

flipback : Bool × ℕ → ℕ × Bool
flipback = λ x → snd x , fst x

comm× : {A B : Set} → A × B → B × A
comm× = λ {(fst₁ , snd₁) → snd₁ , fst₁}

comm×back : {A B : Set} → B × A → A × B
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
ee = inr λ x → exfalso x -- vagy tt

d : (⊤ ⊎ (⊤ × ⊥)) × (⊤ ⊎ ⊥)
d = inl tt , inl tt

from : {A : Set} → A × A → (Bool → A)
from = λ {x false → snd x
        ; x true → fst x}
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

------------------------------------------------------
-- all algebraic laws systematically
------------------------------------------------------

-- (⊎, ⊥) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc⊎ : {A B C : Set} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C)
assoc⊎ = (λ {(inl (inl x)) → inl x
           ; (inl (inr x)) → inr (inl x)
           ; (inr x) → inr (inr x)}) , λ {(inl x) → inl (inl x)
                                        ; (inr (inl x)) → inl (inr x)
                                        ; (inr (inr x)) → inr x}

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
