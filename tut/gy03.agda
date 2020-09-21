module tut.gy03 where

open import lib

-- finite types

from : ℕ × ℕ → (Bool → ℕ)
from = {!!}

to : (Bool → ℕ) → ℕ × ℕ
to = {!!}

-- implicit arguments

comm× : {A B : Set} → A × B → B × A
comm× = {!!}

-- use comm×
usagecomm : ℕ × Bool → Bool × ℕ
usagecomm = {!!}

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

usageassoc : (ℕ × Bool) × (ℕ → ℕ) → ℕ × (Bool × (ℕ → ℕ))
usageassoc = {!!}

idl× : {A : Set} → ⊤ × A ↔ A
idl× = {!!}

idr× : {A : Set} → A × ⊤ ↔ A
idr× = {!!}

-- commutativity above

-- ⊥ is a null element

null× : {A : Set} → A × ⊥ ↔ ⊥
null× = {!!}

-- distributivity of × and ⊎

dist : {A B C : Set} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
dist = {!!}

-- exponentiation laws

curry : {A B C : Set} → ((A × B) → C) ↔ (A → (B → C))
curry = {!!}

⊎×→ : {A B C D : Set} → (A ⊎ B) → C ↔ (A → C) × (B → C)
⊎×→ = {!!}

^0 : {A : Set} → (⊥ → A) ↔ ⊤
^0 = {!!}

^1 : {A : Set} → (⊤ → A) ↔ A
^1 = {!!}

1^ : {A : Set} → (A → ⊤) ↔ ⊤
1^ = {!!}

-- random exercises

forward : (Bool → ℕ) × (Bool → Bool) → ℕ × Bool × ℕ × Bool
forward = {!!}

backward : ℕ × Bool × ℕ × Bool → (Bool → ℕ) × (Bool → Bool)
backward = {!!}

-- extra

-- don't use × or other functions using ×!  NOTE: (Bool → ℕ) contains
-- the same information as (ℕ × ℕ) which contains more information
-- than (ℕ × Bool)
is1 : ℕ → Bool
is1 = {!!}

-- don't use × or other functions using ×!
pred : ℕ → ℕ
pred = {!!}

_>?_ : ℕ → ℕ → Bool
_>?_ = {!!}

dnp : {A : Set} → A → ((A → ⊥) → ⊥)
dnp = {!!}

join : {A : Set} → ((((A → ⊥) → ⊥) → ⊥) → ⊥) → ((A → ⊥) → ⊥)
join = {!!}

--

testfromto1 : {a b : ℕ} → Eq ℕ (proj₁ (to (from (a , b)))) a
testfromto1 = {!!}

testfromto2 : {a b : ℕ} → Eq ℕ (proj₂ (to (from (a , b)))) b
testfromto2 = {!!}

testfromto3 : {a b : ℕ} → Eq ℕ (from (to (λ x → if x then a else b)) true) a
testfromto3 = {!!}

testfromto4 : {a b : ℕ} → Eq ℕ (from (to (λ x → if x then a else b)) false) b
testfromto4 = {!!}

testcomm : {A B : Set}{w : ℕ × Bool} → Eq (ℕ × Bool) (comm× (comm× w)) w
testcomm = {!!}

testassoc× : {A B C : Set}{w : (A × B) × C} → Eq ((A × B) × C) (proj₂ assoc× (proj₁ assoc× w)) w
testassoc× = {!!}

testforward : {w : ℕ × Bool × ℕ × Bool} → Eq _ (forward (backward w)) w
testforward = {!!}

testpred1 : Eq ℕ (pred 0) 0
testpred1 = {!!}

testpred2 : Eq ℕ (pred 1000) 999
testpred2 = {!!}

test>?1 : Eq _ (3 >? 4) false
test>?1 = {!!}

test>?2 : Eq _ (4 >? 1) true
test>?2 = {!!}

test>?3 : Eq _ (1 >? 4) false
test>?3 = {!!}

test>?4 : Eq _ (1 >? 1) false
test>?4 = {!!}
