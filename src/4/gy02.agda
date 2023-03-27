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
flip (n , b) = b , n

-- same scheme
flipback : Bool × ℕ → ℕ × Bool
flipback = {!!}

-- in general:
comm× : {A B : Set} → A × B → B × A
comm× (a , b) = b , a
-- basically, this is the only way it can be defined

comm×back : {A B : Set} → B × A → A × B
comm×back = comm×

--        2  × 1
b1 b2 : Bool × ⊤
b1 = true , tt
b2 = false , tt
b1≠b2 : b1 ≡ b2 → ⊥  --what is this?
b1≠b2 ()
-- b1≠b2 = λ {()}
-- λ { true → ? ; false → ? }

--      1  + 1
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
ee = inr (λ {()})

-- btb : ⊥ → Bool
-- btb _ = true is basically the same as btb _ = false 

-- how many different elements does this type have?
--  (1 +  (1 × 0))  ×  (1 + 0)
d : (⊤ ⊎ (⊤ × ⊥)) × (⊤ ⊎ ⊥)
d = inl tt , inl tt

from : {A : Set} → A × A → (Bool → A)
from (a1 , a2) = λ {true → a1 ; false → a2}
to : {A : Set} → (Bool → A) → A × A
to f = f true , f false
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

-- C-u C-u C-c C-,
assoc⊎ : {A B C : Set} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C)
assoc⊎ = (λ x → case x (λ y → case y (λ a → inl a) λ b → inr (inl b)) λ c → inr (inr c)) ,
          λ { (inl a) → inl (inl a) ; (inr bvc) → case bvc (λ b → inl (inr b)) λ c → inr c }

idl⊎ : {A : Set} → ⊥ ⊎ A ↔ A
idl⊎ = {!!}

-- homework
idr⊎ : {A : Set} → A ⊎ ⊥ ↔ A
idr⊎ = {!!}

-- homework
comm⊎ : {A B : Set} → A ⊎ B ↔ B ⊎ A
comm⊎ = (λ avb → case avb (λ a → inr a) {!!}) , {!!}

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

-- homework
law1^ : {A : Set} → (A → ⊤) ↔ ⊤
law1^ = {!!}

---------------------------------------------------------
-- random isomorphisms
------------------------------------------------------

{-
f : Bool → A ⊎ B
ismered: f true, f false

tfh. f true = inl a1; f false = inl a2
ezt megfeleltetem annak, hogy (if b then a1 else a2)
lesz inl (λ bool → if bool then a1 else a2)

tfh. f true = inl a; f false = inr b
ezt megfeleltetem annak, hogy true , (a , b)

tfh. f true = inr b; f false = inl a
ezt megfeleltetem annak, hogy false , (a , b)

tfh. f true = inl b1; f false = inr b2
ezt megfeleltetem annak, hogy (λ bool → if bool then b1 else b2)
-}

{-
másik irány:
kapok vagy egy inl (booltoa)-t, vagy egy inr (inl boolxaxb)-t, vagy egy inr (inr booltob)-t
ha egy inl (booltoa)-m van: lesz λ bool → if bool then (inl (booltoa true)) else (inl (booltoa false))
ha egy inr (inl (inbool , a , b))-m van: megnézem a boolt
if inbool then
  λ bool → if bool then (inl a) else (inr b)
 else
  λ bool → if bool then (inr b) else (inl a)
ha egy inr (inr booltob)-m van: hasonlóan, mint fönt
-}

iso1 : {A B : Set} → (Bool → (A ⊎ B)) ↔ ((Bool → A) ⊎ ((Bool × A × B) ⊎ (Bool → B)))
iso1 = (λ f → case (f true) (λ a1 → case (f false) (λ a2 → inl λ bool → if bool then a1 else a2)
                                                     λ b2 → inr (inl (true , a1 , b2)))
                             λ b1 → case (f false) (λ a2 → inr (inl (false , a2 , b1)))
                                                     λ b2 → inr (inr λ bool → if bool then b1 else b2)) ,
       {!!}

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
