module gy02 where

open import Lib hiding (comm⊎; flip)

------------------------------------------------------
-- simple finite types
------------------------------------------------------

-- Feladat: Fordítsuk meg egy rendezett pár két komponensét
flip : ℕ × Bool → Bool × ℕ -- (ℕ , Bool) -> (Bool , ℕ)
flip (fst₁ , snd₁) = snd₁ , fst₁

-- Feladat: Fordítsuk meg egy rendezett pár két komponensét
flipback : Bool × ℕ → ℕ × Bool
flipback (fst₁ , snd₁) = snd₁ , fst₁

-- Vegyük észre, hogy az előző két függvényben bármilyen más csúnya dolgot is lehetne csinálni.
-- Írj rá példát itt!

flipback' : Bool × ℕ → ℕ × Bool
flipback' x = 0 , true

-- Feladat: Fordítsuk meg egy rendezett pár két komponensét
comm× : {A B : Set} → A × B → B × A
comm× (fst₁ , snd₁) = snd₁ , fst₁

comm×back : {A B : Set} → B × A → A × B
comm×back (fst₁ , snd₁) = snd₁ , fst₁
-- Ezekben lehetetlen hülyeséget csinálni.
-- Hányféleképpen lehetséges implementálni ezt a két fenti függvényt?


-- ALGEBRAI ADATTÍPUSOK ELEMSZÁMAI:

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

{-
t1 t2 : ⊤ ⊎ ⊤ ⊎ ⊤ 
t1 = inl tt
t2 = inr (inl tt)
t1≠t2 : t1 ≡ t2 → ⊥
t1≠t2 ()
-}

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
d = inl tt , inl tt
-- Ezek alapján hogy lehet megállapítani, hogy melyik típus hány elemű?
-- | ⊤ | = 1
-- | ⊥ | = 0
-- | Bool | = 2
-- | Bool ⊎ ⊤ | = 3
-- | A ⊎ B | = |A| + |B|
-- | A × B | = |A| × |B|
-- | Bool × Bool × Bool | = 8
-- | ⊤ → ⊥ | = 0 = 0 ^ 1
-- | ⊥ → ⊤ | = 1 = 1 ^ 0
-- | ⊥ → ⊥ | = 1 = 0 ^ 0
-- | Bool → ⊥ | = 0 = 0 ^ 2
-- | Bool → ⊤ | = 1 = 1 ^ 2
-- | ⊤ → Bool | = 2 = 2 ^ 1
-- | A → B | = |B| ^ |A|
-- | Bool → Bool → Bool | = |Bool → (Bool → Bool) | = |Bool → Bool| ^ |Bool| = (|Bool| ^ |Bool|) ^ |Bool| = (2 ^ 2) ^ 2 = 4 ^ 2 = 16


-- Ezek alapján milyen matematikai állítást mond ki és bizonyít a lenti állítás?
-- Válasz:
from' : {A : Set} → A × A → (Bool → A)
from' x false = snd x
from' x true = fst x

fth : {A : Set} → A × A → (Bool → A)
fth x x₁ = if x₁ then fst x else snd x

to' : {A : Set} → (Bool → A) → A × A
to' = λ f → f true , f false
testfromto1 : {A : Set}{a b : A} → fst (to' (from' (a , b))) ≡ a
testfromto1 = refl
testfromto2 : {A : Set}{a b : A} → snd (to' (from' (a , b))) ≡ b
testfromto2 = refl
testfromto3 : {A : Set}{a b : A} → from' (to' (λ x → if x then a else b)) true ≡ a
testfromto3 = refl
testfromto4 : {A : Set}{a b : A} → from' (to' (λ x → if x then a else b)) false ≡ b
testfromto4 = refl

------------------------------------------------------
-- all algebraic laws systematically
------------------------------------------------------

-- (⊎, ⊥) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc⊎ : {A B C : Set} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C)

fst assoc⊎ (inl (inl a)) = inl a
fst assoc⊎ (inl (inr b)) = inr (inl b)
fst assoc⊎ (inr b) = inr (inr b)
---
snd assoc⊎ (inl a) = inl (inl a)
snd assoc⊎ (inr (inl a)) = inl (inr a)
snd assoc⊎ (inr (inr b)) = inr b

idl⊎ : {A : Set} → ⊥ ⊎ A ↔ A
--fst idl⊎ x = case x exfalso λ a → a
fst idl⊎ (inr b) = b
snd idl⊎ = inr

idr⊎ : {A : Set} → A ⊎ ⊥ ↔ A
fst idr⊎ (inl a) = a
snd idr⊎ x = inl x

comm⊎ : {A B : Set} → A ⊎ B ↔ B ⊎ A
fst comm⊎ (inl a) = inr a
fst comm⊎ (inr b) = inl b
snd comm⊎ (inl a) = inr a
snd comm⊎ (inr b) = inl b

-- (×, ⊤) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc× : {A B C : Set} → (A × B) × C ↔ A × (B × C)
fst assoc× ((x , z) , y) = x , z , y
snd assoc× (x , y , z) = (x , y) , z

idl× : {A : Set} → ⊤ × A ↔ A
idl× {A} = (λ { (fst₁ , snd₁) → snd₁ }) , f where
  f : A → ⊤ × A
  f x = tt , x

idr× : {A : Set} → A × ⊤ ↔ A
fst idr× x = fst x
snd idr× x = x , tt -- _, tt

-- ⊥ is a null element

null× : {A : Set} → A × ⊥ ↔ ⊥
fst null× ()
snd null× ()

-- distributivity of × and ⊎

dist : {A B C : Set} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
fst dist (😘 , inl a) = inl (😘 , a)
fst dist (😘 , inr b) = inr (😘 , b)
snd dist (inl a) = fst a , inl (snd a)
snd dist (inr b) = (fst b) , inr (snd b)

-- exponentiation laws

curry : ∀{A B C : Set} → (A × B → C) ↔ (A → B → C)
fst curry x c 😘 = x (c , 😘)
snd curry x y = x (fst y) (snd y)

⊎×→ : {A B C D : Set} → ((A ⊎ B) → C) ↔ (A → C) × (B → C)
fst ⊎×→ x = (λ y → x (inl y)) ,  (λ y → x (inr y)) -- x ∘ inr
snd ⊎×→ x z = case z (fst x) (snd x)

law^0 : {A : Set} → (⊥ → A) ↔ ⊤
fst law^0 _ = tt
snd law^0 _ x = exfalso x

law^1 : {A : Set} → (⊤ → A) ↔ A
fst law^1 x = x tt
snd law^1 x _ = x

law1^ : {A : Set} → (A → ⊤) ↔ ⊤
fst law1^ _ = tt
snd law1^ x _ = x

---------------------------------------------------------
-- random isomorphisms
------------------------------------------------------

-- Milyen algebrai állítást mond ki az alábbi típus?
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
  