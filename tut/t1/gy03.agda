module tut.t1.gy03 where

open import lib

-- finite types

-- C-c, C-r

-- adj meg kulonbozo termeket!
a1 a2 a3 a4 a5 : ℕ × Bool
a1 = 1 , true
a2 = 1 , false
a3 = 4 , true
a4 = 9 , false
a5 = 7 , true

-- Bool × Bool
-- true , true
-- false , false
-- true , false
-- ....

-- ⊤ = \top
-- ⊥ = \bot

-- ⊤ × Bool
-- tt , true
-- tt , false
-- ⊤ → A
-- ⊥ × Bool
-- ? , false
-- ? , true
-- if t : ⊥ then exfalso t : A 


-- adj meg kulonbozo termeket!
b1 b2 b3 : Bool ⊎ ⊤
b1 = inj₁ true
b2 = inj₁ false
b3 = inj₂ tt

-- adj meg kulonbozo termeket!
c1 c2 : Bool × ⊤
c1 = {!!}
c2 = {!!}

d : (⊤ ⊎ (⊤ × ⊥)) × (⊤ ⊎ ⊥)
d = inj₁ tt , inj₁ tt

e1 e2 : (⊤ → ⊥) ⊎ Bool
e1 = inj₂ true
e2 = inj₂ false

from : ℕ × ℕ → (Bool → ℕ)
from = λ t → λ b → if b then proj₁ t else proj₂ t

to : (Bool → ℕ) → ℕ × ℕ
to = λ f → f true , f false

fromto : ℕ × ℕ ↔ (Bool → ℕ)
fromto = from , to

-- implicit arguments

comm× : {A B : Set} → A × B → B × A
comm× = λ a×b → proj₂ a×b , proj₁ a×b

-- use comm×
usagecomm : ℕ × Bool → Bool × ℕ
usagecomm = comm×

-- (⊎, ⊥) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc⊎ : {A B C : Set} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C)
assoc⊎ = (λ x → case x
                (λ y → case y inj₁ λ b → inj₂ ((inj₁ b)))
                λ c → inj₂ (inj₂ c)) ,
         {!!}

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
forward = λ u → proj₁ u false , (proj₂ u false , proj₁ u true , proj₂ u true)

backward : ℕ × Bool × ℕ × Bool → (Bool → ℕ) × (Bool → Bool)
backward = λ u → (λ b → if b then proj₁ (proj₂ (proj₂ u)) else proj₁ u)
               , λ b → if b then proj₂ (proj₂ (proj₂ u)) else proj₁ (proj₂ u)

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

bind : {A B : Set} → ((A → ⊥) → ⊥) → (A → (B → ⊥) → ⊥) → (B → ⊥) → ⊥
bind = {!!}

-- return : A → ¬ ¬ A
-- join ¬ ¬ (¬ ¬ A) → ¬ ¬ A
-- bind ¬ ¬ A → (A → ¬ ¬ B) → ¬ ¬ B

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
testforward = refl

--testbackward : {w : (Bool → ℕ) × (Bool → Bool)} → Eq _ (backward (forward w)) w
--testbackward = ?

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


-- assignment
✂ : {A B C : Set} →  A × (B ⊎ C) → ((A → B × ⊤) ⊎ A × C)
✂ = λ x → case (proj₂ x) (λ b → inj₁ λ a → b , tt) (λ c → inj₂ (proj₁ x , c))

-- nagyon extra (egyik nem működik)
dm1 : ∀{A B : Set} → ¬ (A ⊎ B) ↔ ¬ A × ¬ B
dm1 = {!!}

dm2 : ∀{A B : Set} → ¬ (A × B) ↔ ¬ A ⊎ ¬ B
dm2 = {!!}
