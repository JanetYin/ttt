module gy02 where

open import Lib hiding (comm⊎)

-- (λ x → t) y ≝ t [x ↦ y] -- függvény β-szabálya
-- (λ x → f x) ≝ f -- függvény η-szabálya | η = \eta

-- α-konverzió, renaming
id= : ∀{i}{A : Set i} → (λ (x : A) → x) ≡ (λ y → y)
id= = refl

-- Mesélni róla:
-- Függvények β-szabálya, η-szabálya -- ha nem volt még.
-- Esetleg konkrét példán megmutatni.

------------------------------------------------------
-- simple finite types
------------------------------------------------------

{-
-- új típusok:
false true : Bool
× = \x = \times
_×_ rendezett pár; konstruktor _,_
⊤ = \top; konstruktor tt
⊥ = \bot; nincs konstruktor
⊎ = \u+; 2 konstruktor: inl, inr
↔ = \<->; A ↔ B = (A → B) × (B → A)
-}

-- Feladat: Fordítsuk meg egy rendezett pár két komponensét
flip'' : ℕ × Bool → Bool × ℕ
flip'' x = snd x , fst x

-- Feladat: Fordítsuk meg egy rendezett pár két komponensét
flipback : Bool × ℕ → ℕ × Bool
flipback (x , y) = y , x

-- Vegyük észre, hogy az előző két függvényben bármilyen más csúnya dolgot is lehetne csinálni.
-- Írj rá példát itt!

flip-csúnya : Bool × ℕ → ℕ × Bool
flip-csúnya _ = 1 , true

-- Feladat: Fordítsuk meg egy rendezett pár két komponensét
comm× : {A B : Set} → A × B → B × A
comm× (x , y) = y , x

comm×back : {A B : Set} → B × A → A × B
comm×back = comm× 
-- Ezekben lehetetlen hülyeséget csinálni.
-- Hányféleképpen lehetséges implementálni ezt a két fenti függvényt?


-- ALGEBRAI ADATTÍPUSOK ELEMSZÁMAI:

b1 b2 : Bool × ⊤
b1 = false , tt
b2 = true , tt
b1≠b2 : b1 ≡ b2 → ⊥
b1≠b2 ()

t1 t2 : ⊤ ⊎ ⊤
t1 = inl tt
t2 = inr tt
t1≠t2 : t1 ≡ t2 → ⊥
t1≠t2 ()

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

t : Bool → ⊤
t _ = tt

t' : Bool → ⊤
t' false = tt
t' true = tt

-- ⊤ η-szabálya: (a : ⊤) → a ≡ tt
-- | Bool → ⊤ | = 1²

eqqq : t ≡ t'
eqqq = refl

ee : (⊤ → ⊥) ⊎ (⊥ → ⊤)
ee = {!!}

d : (⊤ ⊎ (⊤ × ⊥)) × (⊤ ⊎ ⊥)
d = {!!}
-- Ezek alapján hogy lehet megállapítani, hogy melyik típus hány elemű?
-- | ⊤ | =
-- | ⊥ | =
-- | Bool | =
-- | Bool ⊎ ⊤ | =
-- | A ⊎ B | =
-- | A × B | =
-- | Bool × Bool × Bool | =
-- | ⊤ → ⊥ | =
-- | ⊥ → ⊤ | =
-- | ⊥ → ⊥ | =
-- | Bool → ⊥ | =
-- | Bool → ⊤ | =
-- | ⊤ → Bool | =
-- | A → B | =
-- | Bool → Bool → Bool | =


-- Ezek alapján milyen matematikai állítást mond ki és bizonyít a lenti állítás?
-- Válasz:
from' : {A : Set} → A × A → (Bool → A)
from' = {!!}
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
assoc⊎ = {!!}

idl⊎ : {A : Set} → ⊥ ⊎ A ↔ A
idl⊎ = (λ x → case x (λ t → exfalso t) id) , λ a → inr a

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
