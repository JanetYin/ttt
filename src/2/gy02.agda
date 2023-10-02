open import Lib hiding (comm⊎)


------------------------------------------------------
-- simple finite types
------------------------------------------------------

-- × az mindkettőt tárolja
-- ⊎ csak egyet
--
-- referenciális átlátszóság
-- A

flip : ℕ × Bool → Bool × ℕ -- times, x
flip (n , b) = b , n

flipback : Bool × ℕ → ℕ × Bool
flipback x = snd x , fst x

flipback' : Bool × ℕ → ℕ × Bool
flipback' (n , b) = b , n

comm× : {A B : Set} → A × B → B × A
comm× (a , b) = b , a

comm×back : {A B : Set} → B × A → A × B
comm×back = comm×

top : ⊤ -- űtop
top = tt

-- × = űx
-- ⊤ = űtop
-- ℕ = űbN
-- → = űto vagy űr

b1 b2 : Bool × ⊤ -- × = ,
b1 = true , tt
b2 = false , tt
b1≠b2 : b1 ≡ b2 → ⊥
b1≠b2 ()

--- három ℕ × ⊤ típusú kifejezést amelyek értéke különböző
--- három Bool × Bool típusú kifejezést amelyek értéke különböző
--- ℕ × ⊤ → ⊤ × ℕ típusú függvényt

n1' n2' n3' : ℕ × ⊤
n1' = 3 , tt
n2' = 4 , tt
n3' = 5 , tt

b1' b2' b3' b4' b5' : Bool × Bool
b1' = false , true
b2' = true , true
b3' = true , false
b4' = false , false -- C-c C-n
b5' = fst b1' , snd b2'

t1 t2 : ⊤ ⊎ ⊤ -- űuplus, űu+
-- inl : A → A ⊎ B
-- inr : B → A ⊎ B
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

-- ⊤ ⊎ ℕ, 4 külömböző
-- Bool ⊎ Bool, 4 különböző
n1 n2 n3 n4 : ⊤ ⊎ ℕ
n1 = inl tt
n2 = inr 1
n3 = inr 2
n4 = inr 3

b1'' b2'' b3'' b4'' : Bool ⊎ Bool
b1'' = inl false
b2'' = inl true
b3'' = inr false
b4'' = inr true


ee : (⊤ → ⊥) ⊎ (⊥ → ⊤)
ee = inr (λ x → tt)

d : (⊤ ⊎ (⊤ × ⊥)) × (⊤ ⊎ ⊥)
d = inl tt , inl tt

t : Bool → Bool
t = λ { false → {!!} ; true → {!!}}
-- param elé {
-- lambda után }
-- C-c C-l

from' : {A : Set} → A × A → (Bool → A)
from' (x , y) false = y
from' (x , y) true = x
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

-- inl : A → A ⊎ B
-- inr : B → A ⊎ B

exp : {A B : Set} → ((A × B) ⊎ B) → B
exp (inl a) = snd a
exp (inr b) = b


------------------------------------------------------
-- all algebraic laws systematically
------------------------------------------------------

-- (⊎, ⊥) form a commutative monoid (kommutativ egysegelemes felcsoport)
-- űlr
ttt : ⊤ × ⊤ ↔ ⊤
ttt = (λ x → tt) , λ x → tt , tt

assoc⊎ : {A B C : Set} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C)
assoc⊎ = (λ { (inl (inl a)) → inl a ; (inl (inr b)) → inr (inl b) ; (inr c) → inr (inr c)})
  ,
  λ { (inl a) → inl (inl a) ; (inr (inl a)) → inl (inr a) ; (inr (inr b)) → inr b}

exfalso' : {A : Set} → ⊥ → A
exfalso' ()

case' : {A B C : Set} → (A ⊎ B) → (A → C) → (B → C) → C
case' (inl a) x₁ x₂ = x₁ a
case' (inr b) x₁ x₂ = x₂ b

idl⊎ : {A : Set} → ⊥ ⊎ A ↔ A
fst idl⊎ x = case x (λ x → exfalso x) (λ z → z)
snd idl⊎ = {!!}

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

---
f : {A B C : Set} → (B → A) → A ⊎ B → (C ⊎ C) × ⊤ → A × C
f = λ {
  x (inl a) (inl a₁ , snd₁) → a , a₁ ;
  x (inl a) (inr b , snd₁) → a , b ;
  x (inr b) (inl a , snd₁) → x b , a ;
  x (inr b) (inr b₁ , snd₁) → x b , b₁}


-- data Süti = Almond | ChocolateChip | Raspberry
data Suti : Set where
  Almond : Suti
  ChocolateChip : Suti
  Raspberry : Suti


-- data Tuple a b = (,) a b

data Tuple (A : Set)(B : Set) : Set where
  vesszo : A → B → Tuple A B

-- data Either a b = Left a | Right b

data Either (A : Set)(B : Set) : Set where
  left : A → Either A B
  right : B → Either A B


-- data a <-> b = (a -> b) × (b -> a)

-- űlr

g : {A : Set} → A ↔ A
g = (λ z → z) , λ z → z
