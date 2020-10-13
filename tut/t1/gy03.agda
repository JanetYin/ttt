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
c1 = true , tt
c2 = false , tt

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
         λ x → case x
               (λ a → inj₁ (inj₁ a))
               λ y → case y (λ b → inj₁ (inj₂ b)) inj₂

idl⊎ : {A : Set} → ⊥ ⊎ A ↔ A
idl⊎ = (λ u → case u exfalso λ x → x) , inj₂

idr⊎ : {A : Set} → A ⊎ ⊥ ↔ A
idr⊎ = (λ u → case u (λ x → x) exfalso) , inj₁

comm⊎ : {A B : Set} → A ⊎ B ↔ B ⊎ A
comm⊎ = (λ u → case u inj₂ inj₁)
      , (λ u → case u inj₂ inj₁)

-- (×, ⊤) form a commutative monoid (kommutativ egysegelemes felcsoport)

assoc× : {A B C : Set} → (A × B) × C ↔ A × (B × C)
assoc× = (λ u → (proj₁ (proj₁ u)) , ((proj₂ (proj₁ u)) , (proj₂ u)))
       , λ u → ((proj₁ u) , (proj₁ (proj₂ u))) , (proj₂ (proj₂ u))

-- assoc× implicit paramétereit a typechecker kitalálja
usageassoc : (ℕ × Bool) × (ℕ → ℕ) → ℕ × (Bool × (ℕ → ℕ))
usageassoc = proj₁ assoc×

idl× : {A : Set} → ⊤ × A ↔ A
idl× = proj₂ , (tt ,_)

idr× : {A : Set} → A × ⊤ ↔ A
idr× = proj₁ , (_, tt)

-- commutativity above

-- ⊥ is a null element

null× : {A : Set} → A × ⊥ ↔ ⊥
null× = proj₂ , exfalso

-- distributivity of × and ⊎

dist : {A B C : Set} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
dist = (λ u → case (proj₂ u)
                   (λ b → inj₁ (proj₁ u , b))
                   λ c → inj₂ (proj₁ u , c))
     , λ u → case u
                  (λ v → proj₁ v , inj₁ (proj₂ v))
                  λ v → proj₁ v , inj₂ (proj₂ v)

-- exponentiation laws

curry : {A B C : Set} → ((A × B) → C) ↔ (A → (B → C))
curry = (λ f a b → f (a , b))
      , (λ f ab → f (proj₁ ab) (proj₂ ab))

⊎×→ : {A B C D : Set} → (A ⊎ B) → C ↔ (A → C) × (B → C)
⊎×→ = λ u → (λ c → (λ _ → c) , (λ _ → c))
          , (λ v → case u (proj₁ v) (proj₂ v))

^0 : {A : Set} → (⊥ → A) ↔ ⊤
^0 = (λ _ → tt) , (λ _ → exfalso)

^1 : {A : Set} → (⊤ → A) ↔ A
^1 = (λ f → f tt) , (λ a _ → a)

1^ : {A : Set} → (A → ⊤) ↔ ⊤
1^ = (λ _ → tt) , (λ _ _ → tt)

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
is1 = λ n → rec (λ b → b) (λ f b → if b then false else f true) n false

pred' : ℕ → ℕ
pred' = λ n → proj₂
              (rec {A = Bool × ℕ}
              (true , zero)
              (λ t → false , if proj₁ t then zero else suc (proj₂ t))
              n)

-- lehet, hogy van szebb megoldás, de ebben szerintem nagyon érthető a koncepció
-- a fenti pred'-ből indulunk ki
-- a ~ b jelentése: a-t b-vé kódoljuk (tehát nem jelent egyenlőséget/izomorfizmust/ilyesmit)
-- true ∼ 1
-- false ~ 0
-- Bool × ℕ ∼ Bool → ℕ 
-- proj₁ t ∼ f true
-- proj₂ t ∼ f false
-- t = b , n ∼ f = λ x → if x then b(átírása) else n

-- don't use × or other functions using ×!
pred : ℕ → ℕ
pred = λ n → rec {A = Bool → ℕ}
                 (λ b → if b then suc zero else zero)
                 (λ f b → if b then zero else (if is1 (f true) then zero else suc (f false)) )
                 n
                 false

-- próbáljátok meg esetleg hasonló módon ezt is
_>?_ : ℕ → ℕ → Bool
_>?_ = {!!}


-- plusz feladat, azoknak, akiket ez érdekel:
-- gondoljátok meg, hogy teljesülnek-e a funktor/monád törvények az
-- általatok megadott konstrukciókra

dnp : {A : Set} → A → ((A → ⊥) → ⊥)
dnp = {!!}

join : {A : Set} → ((((A → ⊥) → ⊥) → ⊥) → ⊥) → ((A → ⊥) → ⊥)
join = {!!}

fmap : ∀{A B : Set} → (A → B) → ((A → ⊥) → ⊥) → (B → ⊥) → ⊥
fmap = {!!}

bind : {A B : Set} → ((A → ⊥) → ⊥) → (A → (B → ⊥) → ⊥) → (B → ⊥) → ⊥
bind = {!!}

-- return : A → ¬ ¬ A
-- join ¬ ¬ (¬ ¬ A) → ¬ ¬ A
-- bind ¬ ¬ A → (A → ¬ ¬ B) → ¬ ¬ B

testfromto1 : {a b : ℕ} → Eq ℕ (proj₁ (to (from (a , b)))) a
testfromto1 = refl

testfromto2 : {a b : ℕ} → Eq ℕ (proj₂ (to (from (a , b)))) b
testfromto2 = refl

testfromto3 : {a b : ℕ} → Eq ℕ (from (to (λ x → if x then a else b)) true) a
testfromto3 = refl

testfromto4 : {a b : ℕ} → Eq ℕ (from (to (λ x → if x then a else b)) false) b
testfromto4 = refl

testcomm : {A B : Set}{w : ℕ × Bool} → Eq (ℕ × Bool) (comm× (comm× w)) w
testcomm = refl

testassoc× : {A B C : Set}{w : (A × B) × C} → Eq ((A × B) × C) (proj₂ assoc× (proj₁ assoc× w)) w
testassoc× = refl

testforward : {w : ℕ × Bool × ℕ × Bool} → Eq _ (forward (backward w)) w
testforward = refl

testpred1 : Eq ℕ (pred 0) 0
testpred1 = refl

testpred2 : Eq ℕ (pred 1000) 999
testpred2 = refl

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
-- esetleg gondolkodjatok rajta, hogy hogyan kéne átírni, hogy működjék
dm1 : ∀{A B : Set} → ¬ (A ⊎ B) ↔ ¬ A × ¬ B
dm1 = (λ u → (λ a → u (inj₁ a)) , λ b → u (inj₂ b))
    , (λ u v → case v (proj₁ u) (proj₂ u))

dm2 : ∀{A B : Set} → ¬ (A × B) ↔ ¬ ¬ (¬ A ⊎ ¬ B)
dm2 = (λ u v → v (inj₁ λ a → v (inj₂ λ b → u (a , b))))
    , (λ u v → u λ t → case t (λ f → f (proj₁ v)) λ f → f (proj₂ v))



