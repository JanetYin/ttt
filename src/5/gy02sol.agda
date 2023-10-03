open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Lib.Equality
open import Lib.Bool
open import Lib.Sum hiding (comm⊎)
open import Lib.Sigma
open import Lib.Unit
open import Lib.Empty

--
-- egy definíció megnézése: ráállsz a kurzorral, majd M-pötty
-- vissza: C-x k Enter

------------------------------------------------------
-- simple finite types
------------------------------------------------------

-- \x
tuple : ℕ × Bool
tuple = (4 , true)
proj1 : ℕ
proj1 = fst tuple
proj2 : Bool
proj2 = snd tuple

-- \u+
sum1 sum2 : ℕ ⊎ Bool
sum1 = inl 5
sum2 = inr false

containsNat : ℕ ⊎ Bool -> Bool
containsNat (inl n) = true
containsNat (inr b) = false

sum3 sum4 : ℕ ⊎ ℕ
sum3 = inl 5
sum4 = inr 5

isLeft : ℕ ⊎ ℕ -> Bool
isLeft (inl _) = true
isLeft (inr _) = false

-----------------------------------------

flip : ℕ × Bool → Bool × ℕ
flip (n , b) = {!!} , {!!}

flipback : Bool × ℕ → ℕ × Bool
flipback = {!!}

comm× : {A B : Set} → A × B → B × A
comm× (a , b) = b , a
-- or with fst and snd:
-- comm× t = snd t , fst t

comm×back : {A B : Set} → B × A → A × B
comm×back = comm×

a1 a2 a3 : ⊤ ⊎ Bool
a1 = inl tt
a2 = inr true
a3 = inr false

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

--              2  +  1
bb1 bb2 bb3 : Bool ⊎ ⊤
bb1 = inl false
bb2 = inl true
bb3 = inr tt
bb1≠bb2 : bb1 ≡ bb2 → ⊥
bb1≠bb2 ()
bb1≠bb3 : bb1 ≡ bb3 → ⊥
bb1≠bb3 ()
bb2≠bb3 : bb2 ≡ bb3 → ⊥
bb2≠bb3 ()

ee : (⊤ → ⊥) ⊎ (⊥ → ⊤)     -- \top  \bot
ee = inr λ ()

-- bármit! Például:

data Körtefa : Set where
  k1 k2 k3 : Körtefa

kFromNothing : ⊥ -> Körtefa
kFromNothing = exfalso

--         2       3           3 ^ 2
boolToK : Bool -> Körtefa
boolToK true  = k1
boolToK false = k1

--         |A -> B| = |B| ^ |A|

--  (1 +  (1 * 0))  * (1  + 0)
d : (⊤ ⊎ (⊤ × ⊥)) × (⊤ ⊎ ⊥)
d = inl tt , inl tt

--                 |A| * |A|    |A| ^ 2
-- izomorfizmus

{-
tfh. A = {a1, a2, a3}
Bool -> A: 9 db
true -> a1 és false -> a1
true -> a1 és false -> a2
true -> a1 és false -> a3
...
true -> a3 és false -> a3

A × A: 9 db
a1 , a1
a1 , a2
a1 , a3
...
a3 , a3

-}

from' : {A : Set} → A × A → (Bool → A)
-- C-c C-c "változó neve" Enter
-- from' (a1 , a2) false = a2
-- from' (a1 , a2) true = a1
from' (a1 , a2) = λ {true -> a1; false -> a2}
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

-- Not all ↔'s are isomorphisms!
-- For example:
falseIso : Bool ↔ ⊤
falseIso = (λ _ -> tt) , λ t -> true

-- (⊎, ⊥) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc⊎ : {A B C : Set} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C)    -- \lr
-- assoc⊎ = ? , ?
-- vagy: C-c C-c <nem írok változónevet> Enter
fst assoc⊎ (inl (inl a)) = inl a
fst assoc⊎ (inl (inr b)) = inr (inl b)
fst assoc⊎ (inr c) = inr (inr c)
snd assoc⊎ (inl a) = {!!}
snd assoc⊎ (inr (inl b)) = {!!}
snd assoc⊎ (inr (inr c)) = {!!}

-- NOTE: házi innen

idl⊎ : {A : Set} → ⊥ ⊎ A ↔ A
fst idl⊎ (inl ())
fst idl⊎ (inr b) = {!!}
snd idl⊎ = {!!}

idr⊎ : {A : Set} → A ⊎ ⊥ ↔ A
idr⊎ = {!!}

comm⊎ : {A B : Set} → A ⊎ B ↔ B ⊎ A
comm⊎ = {!!}

-- (×, ⊤) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc× : {A B C : Set} → (A × B) × C ↔ A × (B × C)
assoc× = {!!} , {!!}

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

⊎×→ : {A B C : Set} → ((A ⊎ B) → C) ↔ (A → C) × (B → C)
fst ⊎×→ f = (λ a -> f (inl a)) , λ b -> f (inr b)
-- snd ⊎×→ (f , g) avb = case avb f g
snd ⊎×→ (f , g) (inl a) = f a
snd ⊎×→ (f , g) (inr b) = g b

law^0 : {A : Set} → (⊥ → A) ↔ ⊤
fst law^0 _ = tt
-- snd law^0 t = λ ()
snd law^0 t ()
-- snd law^0 t = exfalso

law^1 : {A : Set} → (⊤ → A) ↔ A
law^1 = {!!}

law1^ : {A : Set} → (A → ⊤) ↔ ⊤
law1^ = {!!}

-- NOTE: házi idáig

---------------------------------------------------------
-- random isomorphisms
------------------------------------------------------

{-
A legyen {a1}
B legyen {b1; b2}

λ {true -> inl a1; false -> inl a1}
λ {true -> inl a1; false -> inr b1}
λ {true -> inl a1; false -> inr b2}
λ {true -> inr b1; false -> inl a1}
...
λ {true -> inr b2; false -> inr b2}



     Bool -> A
inl (λ {true -> a1; false -> a1})
          Bool × A × B
inr (inl (true  , a1 , b1))
         (true  , a1 , b2)
         (false , a1 , b1)
         (false , a1 , b2)

          Bool -> B
inr (inr (λ {true -> b1; false -> b1})
          λ {true -> b1; false -> b2}
          ...
          λ {true -> b2; false -> b2}

bal oldal:
---------------
true    | false
--------------
inl a1  | inl a1
...
---------------

jobb oldal:
---------------
true      false
a1          a1
true      false
b1         b1
b1         b2
b2         b1
b2         b2
Bool   A     B
true   a1    b1
..
--------------

-}

--                         (|A| + |B|)^2                (|A|^2 + 2|A||B| + |B|^2)
iso1 : {A B : Set} → (Bool → (A ⊎ B)) ↔ ((Bool → A) ⊎ Bool × A × B ⊎ (Bool → B))
fst iso1 = {!!}
snd iso1 = {!!}

-- Segítség: kezeljétek a ⊥-ot úgy, mintha egy C változó lenne.
iso2 : {A B : Set} → ((A ⊎ B) → ⊥) ↔ ((A → ⊥) × (B → ⊥))
iso2 = ⊎×→

{-
inl tt; inr (inl tt); inr (inr tt)
   |         |          |
inl true; inl false; inr tt

-}

iso3 : (⊤ ⊎ (⊤ ⊎ ⊤)) ↔ Bool ⊎ ⊤
fst iso3 (inl tt) = inl true
fst iso3 (inr (inl tt)) = inl false
fst iso3 (inr (inr tt)) = inr tt
snd iso3 (inl false) = inr (inl tt)
snd iso3 (inl true) = inl tt
snd iso3 (inr tt) = inr (inr tt)
testiso3 : fst iso3 (inl tt) ≡ fst iso3 (inr (inl tt)) → ⊥
testiso3 ()
testiso3' : fst iso3 (inl tt) ≡ fst iso3 (inr (inr tt)) → ⊥
testiso3' ()
testiso3'' : fst iso3 (inr (inl tt)) ≡ fst iso3 (inr (inr tt)) → ⊥
testiso3'' ()

{-
inl tt; inr (inr tt)

Almafa háromelemű: a1; a2; a3
f1 f2 f3 : ⊤ -> Almafa
f1 = λ {tt -> a1}
f2 = λ {tt -> a2}
f3 = λ {tt -> a3}

Bool -> Almafa
g1 = λ {true -> a1; false -> a1}
g2 = λ {true -> a1; false -> a2}
g3 = λ {true -> a1; false -> a3}
...
g9 = λ {true -> a3; false -> a3}

-}

{-
bal oldal:
λ {tt -> inl tt}
λ {tt -> inr (inr tt)}

inl tt
inr tt
-}

iso4 : (⊤ -> ⊤ ⊎ (⊥ ⊎ ⊤)) ↔ (⊤ ⊎ ⊤)
fst iso4 f = case (f tt) (λ _ -> inl tt) λ bvt -> case bvt exfalso λ _ -> inr tt
snd iso4 (inl tt) = λ {tt -> inl tt}
snd iso4 (inr tt) = λ {tt -> inr (inr tt)}
testiso4 : fst iso4 (λ _ → inl tt) ≡ fst iso4 (λ _ → inr (inr tt)) → ⊥
testiso4 ()
testiso4' : snd iso4 (inl tt) tt ≡ snd iso4 (inr tt) tt → ⊥
testiso4' ()
