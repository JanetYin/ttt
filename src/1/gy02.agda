module gy02 where

open import Lib hiding (comm⊎;comm×;assoc×;curry)

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
ee = inr (λ x → tt)

d : (⊤ ⊎ (⊤ × ⊥)) × (⊤ ⊎ ⊥)
d = (inl tt) , (inl tt)
-- Ezek alapján hogy lehet megállapítani, hogy melyik típus hány elemű?
-- | ⊤ | = 1
-- | ⊥ | = 0 
-- | Bool | = 2 
-- | Bool ⊎ ⊤ | = 3 
-- | A ⊎ B | = |A| + |B|
-- | A × B | = |A| x |B|
-- | Bool × Bool × Bool | = 8
-- | ⊤ → ⊥ | = 0 --0^1?
-- | ⊥ → ⊤ | = 1
-- | ⊥ → ⊥ | = 0
-- | Bool → ⊥ | = 0
-- | Bool → ⊤ | = 2
-- | ⊤ → Bool | = 2
-- | A → B | = |B|^|A|
-- | Bool → Bool → Bool | = 16


-- Ezek alapján milyen matematikai állítást mond ki és bizonyít a lenti állítás?
-- Válasz:
from' : {A : Set} → A × A → (Bool → A)
from' (fst₁ , snd₁) false = snd₁
from' (fst₁ , snd₁) true = fst₁
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
assoc⊎ = (λ abc → case abc (λ ab → case ab (λ a → inl a) (λ b → inr (inl b))) (λ c → inr (inr c))) 
        , λ abc → case abc (λ a → inl (inl a)) λ bc → case bc (λ b → inl (inr b)) (λ c → inr c)

idl⊎ : {A : Set} → ⊥ ⊎ A ↔ A
idl⊎ = (λ x → case x (λ x₁ → exfalso x₁) (λ x₁ → x₁)) , (λ a → inr a)

idr⊎ : {A : Set} → A ⊎ ⊥ ↔ A
idr⊎ = (λ x → case x (λ x₁ → x₁) (λ x₁ → exfalso x₁)) , λ x → inl x

comm⊎ : {A B : Set} → A ⊎ B ↔ B ⊎ A
comm⊎ = (λ x → case x (λ x₁ → inr x₁) (λ x₁ → inl x₁)) , ((λ x → case x (λ x₁ → inr x₁) (λ x₁ → inl x₁)))

-- (×, ⊤) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc× : {A B C : Set} → (A × B) × C ↔ A × (B × C)
assoc× = (λ {((a , b) , c) → a , (b , c)}) , λ {(a , b , c) → (a , b) , c}

idl× : {A : Set} → ⊤ × A ↔ A
idl× = (λ {(tt , a) → a}) , λ x → tt , x

idr× : {A : Set} → A × ⊤ ↔ A
idr× = (λ x → fst x) , (λ x → x , tt)

-- ⊥ is a null element

null× : {A : Set} → A × ⊥ ↔ ⊥
null× = (λ {()}) , λ {x → (exfalso x) , x}

-- distributivity of × and ⊎

dist : {A B C : Set} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
dist = (λ {(a , inl b) → inl (a , b)
         ; (a , inr c) → inr (a , c)}) , λ {(inl (a , b)) → a , (inl b)
                                          ; (inr b) → (fst b) , (inr (snd b))}

-- exponentiation laws

curry : ∀{A B C : Set} → (A × B → C) ↔ (A → B → C)
curry = (λ x x₁ x₂ → x (x₁ , x₂)) , λ x x₁ → x (fst x₁) (snd x₁)

⊎×→ : {A B C D : Set} → ((A ⊎ B) → C) ↔ (A → C) × (B → C)
⊎×→ = (λ x → (λ x₁ → x (inl x₁)) , (λ x₁ → x (inr x₁))) , λ x x₁ →  case x₁ (λ x₂ → fst x x₂) λ x₂ → snd x x₂

law^0 : {A : Set} → (⊥ → A) ↔ ⊤
law^0 = (λ x → tt) , λ x x₁ → exfalso x₁

law^1 : {A : Set} → (⊤ → A) ↔ A
law^1 = (λ x → x tt) , (λ x x₁ → x)

law1^ : {A : Set} → (A → ⊤) ↔ ⊤
law1^ = (λ x → tt) , (λ x x₁ → tt)

---------------------------------------------------------
-- random isomorphisms
------------------------------------------------------

-- Milyen algebrai állítást mond ki az alábbi típus?
iso1 : {A B : Set} → (Bool → (A ⊎ B)) ↔ ((Bool → A) ⊎ Bool × A × B ⊎ (Bool → B))
fst iso1 x with x true | x false 
... | inl a | inl a₁ = inl (λ x₁ → a)
... | inl a | inr b = inr (inl (true , (a , b)))
... | inr b | inl a = inr (inl (false , (a , b)))
... | inr b | inr b₁ = inr (inr (λ x₁ → b)) 
snd iso1 (inl a) = λ x → inl (a x)
snd iso1 (inr (inl (fst₁ , snd₁))) = λ x → if x then (inl (fst snd₁)) else inr (snd snd₁)
snd iso1 (inr (inr b)) = λ x → inr (b x)

iso2 : {A B : Set} → ((A ⊎ B) → ⊥) ↔ ((A → ⊥) × (B → ⊥))
fst iso2 x = (λ x₁ → exfalso (x (inl x₁))) , λ x₁ → exfalso (x (inr x₁))
snd iso2 (fst₁ , snd₁) x₁ = case x₁ fst₁ snd₁

iso3 : (⊤ ⊎ ⊤ ⊎ ⊤) ↔ Bool ⊎ ⊤
fst iso3 (inl a) = inl true
fst iso3 (inr (inl a)) = inl false
fst iso3 (inr (inr b)) = inr tt
snd iso3 (inl false) = inl tt
snd iso3 (inl true) = inl tt
snd iso3 (inr b) = inr (inr tt)
--iso3 = (λ x → case x (λ x₁ → inl (case x (λ x₂ → true) λ x₂ → false)) (λ x₁ → inr tt)) , {!   !}


testiso3 : fst iso3 (inl tt) ≡ fst iso3 (inr (inl tt)) → ⊥
testiso3 ()
testiso3' : fst iso3 (inl tt) ≡ fst iso3 (inr (inr tt)) → ⊥
testiso3' ()
testiso3'' : fst iso3 (inr (inl tt)) ≡ fst iso3 (inr (inr tt)) → ⊥
testiso3'' ()

iso4 : (⊤ → ⊤ ⊎ ⊥ ⊎ ⊤) ↔ (⊤ ⊎ ⊤)
fst iso4 x with x tt
... | inl a = inl tt
... | inr (inr b) = inr tt
snd iso4 (inl a) x₁ = inl tt
snd iso4 (inr b) x₁ = inr (inr tt)

testiso4 : fst iso4 (λ _ → inl tt) ≡ fst iso4 (λ _ → inr (inr tt)) → ⊥
testiso4 ()
testiso4' : snd iso4 (inl tt) tt ≡ snd iso4 (inr tt) tt → ⊥
testiso4' ()
 