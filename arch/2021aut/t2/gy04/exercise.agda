module 2021aut.t2.gy04.exercise where
open import lib

---------------------------------------------------------
-- ⊤,⊥,⊎ tipusok
---------------------------------------------------------

-- adj meg kulonbozo termeket!
bb1 bb2 : 𝟚 ⊎ ⊤
bb1 = {!!}
bb2 = {!!}

-- adj meg kulonbozo termeket!
c1 c2 : 𝟚 × ⊤
c1 = {!!}
c2 = {!!}

d : (⊤ ⊎ (⊤ × ⊥)) × (⊤ ⊎ ⊥)
d = {!!}

-- adj meg kulonbozo termeket!
e1 e2 : (⊤ → ⊥) ⊎ 𝟚
e1 = {!!}
e2 = {!!}

-- ugy add meg from-t es to-t, hogy a tesztek mukodjenek
from : ℕ × ℕ → (𝟚 → ℕ)
from = {!!}

to : (𝟚 → ℕ) → ℕ × ℕ
to = {!!}

testfromto1 : {a b : ℕ} → Eq ℕ (π₁ (to (from (a , b)))) a
testfromto1 = {!!}
testfromto2 : {a b : ℕ} → Eq ℕ (π₂ (to (from (a , b)))) b
testfromto2 = {!!}
testfromto3 : {a b : ℕ} → Eq ℕ (from (to (λ x → if x then a else b)) tt) a
testfromto3 = {!!}
testfromto4 : {a b : ℕ} → Eq ℕ (from (to (λ x → if x then a else b)) ff) b
testfromto4 = {!!}

---------------------------------------------------------
-- implicit arguments
---------------------------------------------------------

comm× : {A B : Set} → A × B → B × A
comm× = {!!}

-- use comm×
usagecomm : ℕ × 𝟚 → 𝟚 × ℕ
usagecomm = {!!}

testcomm : {A B : Set}{w : ℕ × 𝟚} → Eq (ℕ × 𝟚) (comm× (comm× w)) w
testcomm = {!!}

---------------------------------------------------------
-- a tipusok algebrai strukturaja
---------------------------------------------------------

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

testassoc× : {A B C : Set}{w : (A × B) × C} → Eq ((A × B) × C) (π₂ assoc× (π₁ assoc× w)) w
testassoc× = {!!}

usageassoc : (ℕ × 𝟚) × (ℕ → ℕ) → ℕ × (𝟚 × (ℕ → ℕ))
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

-- curry-uncurry (see above)

⊎×→ : {A B C D : Set} → ((A ⊎ B) → C) ↔ (A → C) × (B → C)
⊎×→ = {!!}

^0 : {A : Set} → (⊥ → A) ↔ ⊤
^0 = {!!}

^1 : {A : Set} → (⊤ → A) ↔ A
^1 = {!!}

1^ : {A : Set} → (A → ⊤) ↔ ⊤
1^ = {!!}

---------------------------------------------------------
-- extra exercises
---------------------------------------------------------

-- don't use × or other functions using ×!  NOTE: (𝟚 → ℕ) contains
-- the same information as (ℕ × ℕ) which contains more information
-- than (ℕ × 𝟚)
is1' : ℕ → 𝟚
{-
is1' zero = ff
is1' (suc zero) = tt
is1' (suc (suc zero)) = ff
is1' (suc (suc (suc n))) = is1' (suc (suc n))
-}
--x = is1' c -- n = x - 3
--is1' = λ n → rec {Agda.Primitive.lzero} {𝟚} {!!} {!!} n
is1' n = case t (λ x → ff) λ x → case x (λ x₁ → {-t=ι₂ ι₁ triv-} tt) λ x₁ → ff
  where
  t : ⊤ ⊎ (⊤ ⊎ ⊤)
  t = rec ( ι₁ triv ) (λ uplus → ι₂ (case uplus (λ top → ι₁ triv) λ uplus' → case uplus' ({-ι₂ (ι₁ triv)-} λ top → ι₂ triv) ({-ι₂ (ι₂ triv)-} λ top → ι₂ triv))) n
  -- n=0 → t = ι₁ triv
  -- n=1 → t = ι₂ (ι₁ triv)
  -- n=2 → t = ι₂ (ι₂ triv)
  -- n=3 → t = ι₂ (ι₂ triv)
-- x=1 ↔ x≠0 ⋀ ¬ (x>1)
--is1' n = {! rec ? ? ?!}

{-
/ℕ\
|0| ->  0 ⊤
| |    /ℕ\
|1| -> |0|
|2| -> |1|
|3| -> |2|
...
-}

-- don't use × or other functions using ×!
pred' : ℕ → ℕ
pred' n = let
  t : ⊤ ⊎ ℕ
  t = rec (ι₁ triv) (λ x → case x (λ ι₁triv → ι₂ zero) (λ ι₂n → ι₂ (ι₂n))) n
  in case t {!!} {!!}

testpred'1 : Eq ℕ (pred' 0) 0
testpred'1 = {!!}
testpred'2 : Eq ℕ (pred' 1000) 999
testpred'2 = {!!}

_>?_ : ℕ → ℕ → 𝟚
_>?_ = {!!}

test>?1 : Eq _ (3 >? 4) ff
test>?1 = {!!}
test>?2 : Eq _ (4 >? 1) tt
test>?2 = {!!}
test>?3 : Eq _ (1 >? 4) ff
test>?3 = {!!}
test>?4 : Eq _ (1 >? 1) ff
test>?4 = {!!}

dnp : {A : Set} → A → ((A → ⊥) → ⊥)
dnp = {!!}

join : {A : Set} → ((((A → ⊥) → ⊥) → ⊥) → ⊥) → ((A → ⊥) → ⊥)
join = {!!}

---------------------------------------------------------
-- random isomorphisms
---------------------------------------------------------

--          42         43      a , b , c , d
forward : (𝟚 → ℕ) × (𝟚 → 𝟚) → ℕ × 𝟚 × ℕ × 𝟚
--              a         b         c         d  
forward = λ t → π₁ t tt , π₂ t tt , π₁ t ff , π₂ t ff

backward : ℕ × 𝟚 × ℕ × 𝟚 → (𝟚 → ℕ) × (𝟚 → 𝟚)
backward = λ { (a , b , c , d) →
  (λ x → if x then a else c)
  ,
  (λ x → if x then b else d)
  }

testforward : {w : ℕ × 𝟚 × ℕ × 𝟚} → Eq _ (forward (backward w)) w
testforward = refl

iso1 : {A B : Set} → (𝟚 → (A ⊎ B)) ↔ ((𝟚 → A) ⊎ 𝟚 × A × B ⊎ (𝟚 → B))
iso1 = _,_
  --                    a₁       a₂  b₁       b₂
  -- (𝟚 → A ⊎ B) → (𝟚 → A) ⊎ 𝟚 × A × B ⊎ (𝟚 → B)
  (λ f → case (f {!π₂ iso1!}) (λ a → ι₁ (λ x → a)) (λ b → ι₂ (ι₂ (λ x → b))))
  λ t → λ x → case t
    --        a₁
    (λ f → ι₁ (f x))
     λ t' → case t'
     --          a₂  b₁
      (λ { t'' → π₂ iso1 ({!!}) x})
      --        b₂
       λ f → ι₂ (f x)

iso2 : {A B : Set} → ((A ⊎ B) → ⊥) ↔ ((A → ⊥) × (B → ⊥))
iso2 = {!!}

iso3 : (⊤ ⊎ ⊤ ⊎ ⊤) ↔ 𝟚 ⊎ ⊤
iso3 = {!!}

testiso3 : Eq _ (π₂ iso3 (π₁ iso3 (ι₁ triv))) (ι₁ triv)
testiso3 = refl
testiso3' : Eq _ (π₂ iso3 (π₁ iso3 (ι₂ (ι₁ triv)))) (ι₂ (ι₁ triv))
testiso3' = refl
testiso3'' : Eq _ (π₂ iso3 (π₁ iso3 (ι₂ (ι₂ triv)))) (ι₂ (ι₂ triv))
testiso3'' = refl

iso4 : (⊤ → ⊤ ⊎ ⊥ ⊎ ⊤) ↔ ⊤ ⊎ ⊤
iso4 = {!!}

testiso4 : Eq _ (π₁ iso4 (π₂ iso4 (ι₁ triv))) (ι₁ triv)
testiso4 = {!!}
testiso4' : Eq _ (π₁ iso4 (π₂ iso4 (ι₂ triv))) (ι₂ triv)
testiso4' = {!!}


---------------------------------------------------------
-- subtyping
---------------------------------------------------------

subt-prod : {A A' B B' : Set} → (A → A') → (B → B') → A × B → A' × B'
subt-prod = λ A<A' B<B' w → (A<A' (π₁ w)) , (B<B' (π₂ w))

subt-sum : {A A' B B' : Set} → (A → A') → (B → B') → A ⊎ B → A' ⊎ B'
subt-sum = λ A<A' B<B' w → case w (λ a → ι₁ (A<A' a)) λ b → ι₂ (B<B' b)

subt-top : {A : Set} → A → ⊤
subt-top = λ _ → triv

subt-bot : {A : Set} → ⊥ → A
subt-bot = λ b → exfalso b

subt-fun : {A A' B B' : Set} → (A → A') → (B → B') → (A' → B) → (A → B')
subt-fun = λ A<A' B<B' f a → B<B' (f (A<A' a))
