module gy02 where

open import Lib hiding (flip; comm⊎)

------------------------------------------------------
-- simple finite types
------------------------------------------------------

-- \x
-- Feladat: Fordítsuk meg egy rendezett pár két komponensét
flip : ℕ × Bool → Bool × ℕ
flip (n , b) = b , n

-- Feladat: Fordítsuk meg egy rendezett pár két komponensét
flipback : Bool × ℕ → ℕ × Bool
flipback (b , n) = n , b

-- Vegyük észre, hogy az előző két függvényben bármilyen más csúnya dolgot is lehetne csinálni.
-- Írj rá példát itt!

flip-1 : ℕ × Bool → Bool × ℕ
flip-1 x = (false , 0)

-- A × B × C ≡ A × (B × C) tehát jobbra zárójelezett
pelda : {A B C : Set} → A × (B × C) → A
pelda (fst₁ , snd₁) = fst₁

-- Feladat: Fordítsuk meg egy rendezett pár két komponensét
comm× : {A B : Set} → A × B → B × A
comm× (a , b) = b , a

comm×back : {A B : Set} → B × A → A × B
comm×back (b , a) = a , b
-- Ezekben lehetetlen hülyeséget csinálni.
-- Hányféleképpen lehetséges implementálni ezt a két fenti függvényt?


-- ALGEBRAI ADATTÍPUSOK ELEMSZÁMAI:

-- \top
b1 b2 : Bool × ⊤
b1 = true , tt
b2 = false , tt
b1≠b2 : b1 ≡ b2 → ⊥
b1≠b2 ()

-- \u+
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

-- exfalso a mágikus kalap, amiből egy ⊥ (bottom) segítségével bármit elő tudunk varázsolni
ee : (⊤ → ⊥) ⊎ (⊥ → ⊤)
ee = inr λ x → exfalso x

d : (⊤ ⊎ (⊤ × ⊥)) × (⊤ ⊎ ⊥)
d = inl tt , inl tt
-- Ezek alapján hogy lehet megállapítani, hogy melyik típus hány elemű?
-- | ⊤ | = 1
-- | ⊥ | = 0
-- | Bool | = 2
-- | Bool ⊎ ⊤ | = 3
-- | A ⊎ B | = |A| + |B|
-- | A × B | = |A| * |B|
-- | Bool × Bool × Bool | = 8 = 2 * 2 * 2 = 2 ^ 3
-- | ⊤ → ⊥ | = 0
-- | ⊥ → ⊤ | = 1
-- | ⊥ → ⊥ | = 1
-- | Bool → ⊥ | = 0
-- | Bool → ⊤ | = 1
-- | ⊤ → Bool | = 2
-- | A → B | = |B| ^ |A|
-- | Bool → Bool → Bool | = 2 ^ 2 ^ 2 = 16

-- általános képletek:
-- | A ⊎ B | = |A| + |B|
-- | A × B | = |A| * |B|
-- | A → B | = |B| ^ |A|

-- Ezek alapján milyen matematikai állítást mond ki és bizonyít a lenti állítás?
-- Válasz: A² = A * A
from' : {A : Set} → A × A → (Bool → A)
from' (a , a₁) false = a₁
from' (a , a₁) true = a
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

-- A ↔ B : (A → B , B → A)

assoc⊎ : {A B C : Set} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C)
fst assoc⊎ (inl (inl a)) = inl a
fst assoc⊎ (inl (inr b)) = inr (inl b)
fst assoc⊎ (inr c) = inr (inr c)
snd assoc⊎ (inl a) = inl (inl a)
snd assoc⊎ (inr (inl b)) = inl (inr b)
snd assoc⊎ (inr (inr c)) = inr c

idl⊎ : {A : Set} → ⊥ ⊎ A ↔ A
idl⊎ = (λ {(inr a) → a}) , λ x → inr x

idr⊎ : {A : Set} → A ⊎ ⊥ ↔ A
idr⊎ = (λ where (inl a) → a) , λ x → inl x

comm⊎ : {A B : Set} → A ⊎ B ↔ B ⊎ A
fst comm⊎ (inl a) = inr a
fst comm⊎ (inr b) = inl b
snd comm⊎ (inl b) = inr b
snd comm⊎ (inr a) = inl a

-- (×, ⊤) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc× : {A B C : Set} → (A × B) × C ↔ A × (B × C)
fst assoc× ((a , b) , c) = a , (b , c)
snd assoc× (a , (b , c)) = (a , b) , c

idl× : {A : Set} → ⊤ × A ↔ A
fst idl× (t , a) = a
snd idl× a = tt , a

idr× : {A : Set} → A × ⊤ ↔ A
fst idr× (a , t) = a
snd idr× a = a , tt

-- ⊥ is a null element
null× : {A : Set} → A × ⊥ ↔ ⊥
fst null× () -- absurd pattern, azaz nem tudunk rá helyes mintaillesztést adni (bottomnak nincsen eleme), ilyenkor nincs jobboldal
snd null× x = exfalso x , x -- itt is lehetet volna akár x-re mintát illeszteni, és akkor itt is abszurd mintát kaptunk volna

-- distributivity of × and ⊎

dist : {A B C : Set} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
fst dist (a , inl b) = inl (a , b)
fst dist (a , inr c) = inr (a , c)
snd dist (inl (a , b)) = a , inl b
snd dist (inr (a , c)) = a , inr c

-- exponentiation laws

curry : ∀{A B C : Set} → (A × B → C) ↔ (A → B → C)
fst curry x a b = x (a , b)
snd curry x (a , b) = x a b

⊎×→ : {A B C D : Set} → ((A ⊎ B) → C) ↔ (A → C) × (B → C)
fst ⊎×→ x = (λ a → x (inl a)) , λ b → x (inr b)
snd ⊎×→ (af , bf) (inl a) = af a
snd ⊎×→ (af , bf) (inr b) = bf b

law^0 : {A : Set} → (⊥ → A) ↔ ⊤
fst law^0 x = tt
snd law^0 x x₁ = exfalso x₁ -- vagy mintaillesztés x₁-re, és megint abszurd minta

law^1 : {A : Set} → (⊤ → A) ↔ A
fst law^1 x = x tt
snd law^1 x x₁ = x

law1^ : {A : Set} → (A → ⊤) ↔ ⊤
fst law1^ x = tt
snd law1^ x x₁ = x

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
   