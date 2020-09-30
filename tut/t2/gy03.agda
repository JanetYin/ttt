module tut.t2.gy03 where

open import lib

-- finite types

-- adj meg kulonbozo termeket!
a1 a2 a3 a4 a5 : ℕ × Bool
a1 = 1 , true
a2 = 1 , false
a3 = 2 , true
a4 = 3 , true
a5 = 4 , true

-- adj meg kulonbozo termeket!
b1 b2 : Bool ⊎ ⊤
b1 = inj₁ true
b2 = inj₁ false

-- adj meg kulonbozo termeket!
c1 c2 : Bool × ⊤
c1 = true , tt
c2 = false , tt

d : (⊤ ⊎ (⊤ × ⊥)) × (⊤ ⊎ ⊥)
d = inj₁ tt , inj₁ tt

e1 e2 : (⊤ → ⊥) ⊎ Bool
e1 = inj₂ true
e2 = inj₂ false

from : ℕ × ℕ → (Bool → ℕ)
from = λ p → λ b → if b then proj₁ p else proj₂ p

to : (Bool → ℕ) → ℕ × ℕ
to = λ f → f true , f false

-- implicit arguments

comm× : {A B : Set} → A × B → B × A
comm× = λ axb → proj₂ axb , proj₁ axb

-- use comm×
usagecomm : ℕ × Bool → Bool × ℕ
usagecomm = comm×

-- (⊎, ⊥) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc⊎ : {A B C : Set} → (A ⊎ B) ⊎ C ↔ A ⊎ (B ⊎ C)
assoc⊎ = (λ abc →  case abc
                        (λ ab → case ab (λ a → inj₁ a) λ b → inj₂ (inj₁ b))
                        λ c → inj₂ (inj₂ c))
         ,
          λ abc → case abc
                        (λ a → inj₁ (inj₁ a))
                        λ bc → case bc (λ b → inj₁ (inj₂ b)) λ c → inj₂ c

idl⊎ : {A : Set} → ⊥ ⊎ A ↔ A
idl⊎ = (λ ba → case ba exfalso λ x → x )
       ,
       inj₂

idr⊎ : {A : Set} → A ⊎ ⊥ ↔ A
idr⊎ = (λ ab → case ab (λ x → x) exfalso)
       ,
       inj₁

comm⊎ : {A B : Set} → A ⊎ B ↔ B ⊎ A
comm⊎ = (λ ab → case ab inj₂ inj₁)
        ,
        λ ba → case ba inj₂ inj₁

-- (×, ⊤) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc× : {A B C : Set} → (A × B) × C ↔ A × (B × C)
assoc× = (λ abc → proj₁ (proj₁ abc) , proj₂ (proj₁ abc) , proj₂ abc)
         ,
         {!!} -- TODO...

usageassoc : (ℕ × Bool) × (ℕ → ℕ) → ℕ × (Bool × (ℕ → ℕ))
usageassoc = proj₁ assoc×

idl× : {A : Set} → ⊤ × A ↔ A
idl× = (λ ta → proj₂ ta) , λ a → tt , a

idr× : {A : Set} → A × ⊤ ↔ A
idr× = proj₁ , λ a → a , tt

-- commutativity above

-- ⊥ is a null element

null× : {A : Set} → A × ⊥ ↔ ⊥
null× = (λ ab → proj₂ ab) , exfalso

-- distributivity of × and ⊎

dist : {A B C : Set} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
dist = {!!}

-- exponentiation laws

curry : {A B C : Set} → ((A × B) → C) ↔ (A → (B → C))
curry = (λ abc a b → abc (a , b)) , λ abc ab → abc (proj₁ ab) (proj₂ ab)

⊎×→ : {A B C D : Set} → ((A ⊎ B) → C) ↔ (A → C) × (B → C)
⊎×→ = (λ abc → (λ a → abc (inj₁ a)) , {!!} )
      ,
      λ b ab → case ab (proj₁ b ) (proj₂ b)

^0 : {A : Set} → (⊥ → A) ↔ ⊤
^0 = (λ _ → tt) , λ _ → exfalso

^1 : {A : Set} → (⊤ → A) ↔ A
^1 = (λ f → f tt) , λ a _ → a

1^ : {A : Set} → (A → ⊤) ↔ ⊤
1^ = (λ _ → tt) , λ _ _ → tt

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
