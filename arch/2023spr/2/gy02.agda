open import lib

------------------------------------------------------
-- simple finite types
------------------------------------------------------

flip : ℕ × Bool → Bool × ℕ
flip = λ (x , y) → y , x

flipback : Bool × ℕ → ℕ × Bool
flipback = λ (x , y) → (y , x)

comm× : {A B : Set} → A × B → B × A
comm× (fst , snd) = (snd , fst)

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
ee = inr λ x → tt

d : (⊤ ⊎ (⊤ × ⊥)) × (⊤ ⊎ ⊥)
d = (inl tt) , (inl tt)

from : {A : Set} → A × A → (Bool → A)
from = λ {(fst₁ , snd₁) false → snd₁
        ; (fst₁ , snd₁) true → fst₁}
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
idl⊎ = (λ {(inr x) → x}) , λ x → inr x

idr⊎ : {A : Set} → A ⊎ ⊥ ↔ A
idr⊎ = (λ {(inl x) → x}) , λ x → inl x

comm⊎ : {A B : Set} → A ⊎ B ↔ B ⊎ A
comm⊎ = (λ {(inl x) → inr x
          ; (inr x) → inl x}) , λ {(inl x) → inr x
                                 ; (inr x) → inl x}

-- (×, ⊤) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc× : {A B C : Set} → (A × B) × C ↔ A × (B × C)
assoc× = {!   !}

idl× : {A : Set} → ⊤ × A ↔ A
idl× = {!   !}

idr× : {A : Set} → A × ⊤ ↔ A
idr× = {!   !}

-- ⊥ is a null element

null× : {A : Set} → A × ⊥ ↔ ⊥
null× = {!   !}

-- distributivity of × and ⊎

dist : {A B C : Set} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
dist = {!   !}

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

-- |Bool| = 2
-- |⊤| = 1
-- |Bool × ⊤| = |Bool| * |⊤|
-- |Bool → ⊤| = |⊤| ^ |Bool| 
-- f : Bool → ⊤
-- f _ = tt

iso1 : {A B : Set} → (Bool → (A ⊎ B)) ↔ ((Bool → A) ⊎ Bool × A × B ⊎ (Bool → B))
iso1 {A} {B} = to' , from' where
  to' : (Bool → (A ⊎ B)) → ((Bool → A) ⊎ Bool × A × B ⊎ (Bool → B))
  to' f with f false
  ...| inl a = inl (λ _ → a)
  ...| inr b = inr (inr (λ _ → b))
  -- to' f = case (f false) (λ a → inl λ _ → a) (λ b → inr (inr λ _ → b))
  -- Ezzel nem egészen bizonyítható izomorfan a dolog.
  -- Mindenképpen kéne hozzá az `f true` is, hogy "jól" lehessen bizonyítani.

  from' : ((Bool → A) ⊎ Bool × A × B ⊎ (Bool → B)) → (Bool → (A ⊎ B))
  from' x = {!   !}

iso2 : {A B : Set} → ((A ⊎ B) → ⊥) ↔ ((A → ⊥) × (B → ⊥))
iso2 = {!!}

iso3 : (⊤ ⊎ ⊤ ⊎ ⊤) ↔ Bool ⊎ ⊤
iso3 = (λ where (inl tt) → inl true
                (inr (inl tt)) → inl false
                (inr (inr tt)) → inr tt )
      , 
       (λ x → {!   !}) -- visszafelé "megfordítjuk a felső lambda nyilait"

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