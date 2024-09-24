module gy06-pre where

open import Lib hiding (minMax;CoVec)
import Lib.Containers.List as L
open L using (List; []; _∷_; length)
import Lib.Containers.Vector as V
open V using (Vec; []; _∷_)

---------------------------------------------------------
-- Sigma types
---------------------------------------------------------

-- Vissza a Vec-hez

fromList : {A : Set}(as : List A) → Vec A (length as)
fromList [] = []
fromList (x ∷ as) = x ∷ (fromList as)

-- ..., de függőtípusos rendezett párral.
{-
record
-}
what : Σ ℕ (Vec Bool)
what = {!   !} , {!   !}

filter : {A : Set}{n : ℕ}(f : A → Bool) → Vec A n → Σ ℕ (λ k → Vec A k) -- ezen lehet pontosítani, hiszen n elemnél nem kéne legyen benne több elem soha.
filter f [] = zero , []
filter f (x ∷ x₁) with f x 
... | false = filter f x₁
... | true = suc (fst (filter f x₁)) , x ∷ (snd (filter f x₁)) 

test-filter : filter {ℕ} (3 <ᵇ_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ (2 , 4 ∷ 5 ∷ [])
test-filter = refl

smarterLengthVec : ∀{i}{A : Set i}{n : ℕ} → Vec A n → {!    !}
smarterLengthVec = {!   !}

minMax' : ℕ → ℕ → ℕ × ℕ
minMax' n m = {!   !}

-- Ugyanez sokkal jobban, de leginkább pontosabban.
-- Az előző változatban vissza tudok adni csúnya dolgokat is.
-- Pl. konstans (0 , 0)-t.
minMax : (n m : ℕ) → {!!}
minMax n m = {!   !}

---------------------------------------------------------

Σ=⊎ : {A B : Set} → Σ Bool (if_then A else B) ↔ A ⊎ B
fst Σ=⊎ (false , itl) = inr itl
fst Σ=⊎ (true , itl) = inl itl
snd Σ=⊎ (inl a) = true , a
snd Σ=⊎ (inr b) = false , b

Σ=× : {A B : Set} → Σ A (λ _ → B) ↔ A × B
fst Σ=× (a , b) = a , b
snd Σ=× (a , b) = a , b

-- Π A F is essentially (a : A) → F a
-- what does this mean?

                    -- Π A (λ _ → B)
Π=→ : {A B : Set} → ((a : A) → (λ _ → B) a) ≡ (A → B)
Π=→ {A} {B} = refl

                    -- Π Bool (if_then A else B)
→=× : {A B : Set} → ((b : Bool) → if b then A else B) ↔ A × B
fst →=× x = (x true) , (x false)
snd →=× (a , b) false = b
snd →=× (a , b) true = a

dependentCurry : {A : Set}{B : A → Set}{C : (a : A) → B a → Set} →
  ((a : A)(b : B a) → C a b) ↔ ((w : Σ A B) → C (fst w) (snd w))
fst dependentCurry x w = x (fst w) (snd w)
snd dependentCurry x a b = x (a , b)

------------------------------------------------------
-- Conat -- Pihenés
------------------------------------------------------
{-
IsNotZero∞' : ℕ∞ → Set
IsNotZero∞' n = {!!}
-}

------------------------------------------------------
-- CoVec -- NEM lesz vizsgában, csak érdekesség most.
------------------------------------------------------

infixr 5 _∷_
record CoVec {ℓ}(A : Set ℓ) (n : ℕ∞) : Set ℓ where
  coinductive
  constructor _∷_
  field
    head : .⦃ IsNotZero∞ n ⦄ → A
    tail : .⦃ IsNotZero∞ n ⦄ → CoVec A (pred∞'' (pred∞ n))

  []' : {!!}
  []' = {!!}

open CoVec public
-- \{{ = ⦃
-- \}} = ⦄

[1] : CoVec ℕ 1
[1] = {!!}

replicate : ∀{i}{A : Set i} → {!!}
replicate n a = {!!}

map : ∀{i j}{A : Set i}{B : Set j}{n : ℕ∞} → {!!}
map = {!!}

---------------------------------------------------------
-- propositional logic -- Innentől lefelé lesz vizsgában.
---------------------------------------------------------

-- Curry-Howard izomorfizmus
-- Elmélet:
--   ∙ átalakítani logikai állításokat típusokra.
--   ∙ formalizálni állításokat típusokkal.
--   × = ∧ = konjunkció
--   ⊎ = ∨ = diszjunkció
--   ¬ = ¬ = negáció
--   ⊃ = → = implikáció

subt-prod : {A A' B B' : Set} → (A → A') → (B → B') → A × B → A' × B'
subt-prod x x₁ x₂ = (x (fst x₂)) , (x₁ (snd x₂))

subt-fun : {A A' B B' : Set} → (A → A') → (B → B') → (A' → B) → (A → B')
subt-fun a' b' b a = b' (b (a' a))

anything : {X Y : Set} → ¬ X → X → Y
anything x x₁ = exfalso (x x₁)

ret : {X : Set} → X → ¬ ¬ X
ret x x₁ = x₁ x

-- Másik irány?

fun : {X Y : Set} → (¬ X) ⊎ Y → (X → Y)
fun (inl a) x₁ = anything a x₁
fun (inr b) x₁ = b

-- De Morgan

dm1 : {X Y : Set} →  ¬ (X ⊎ Y) ↔ ¬ X × ¬ Y
fst (fst dm1 x) x₁ = x (inl x₁)
snd (fst dm1 x) x₁ = x (inr x₁)
snd dm1 x (inl a) = fst x a
snd dm1 x (inr b) = snd x b

dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 (inl a) (x₁ , y₁) = a x₁
dm2 (inr b) (x₁ , y₁) = b y₁

dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b x = x (λ x₁ → (inl λ x₂ → x (λ x₃ → (inr λ x₄ → x₃ (x₂ , x₄)))))

-- stuff

nocontra : {X : Set} → ¬ (X ↔ ¬ X)
nocontra (fst₁ , snd₁) = fst₁ (snd₁ λ x → fst₁ x x) (snd₁ (λ x → fst₁ x x))

¬¬invol₁ : {X : Set} → ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
¬¬invol₁ = (λ x x₁ →  x (λ x₂ → x₂ x₁)) , λ x x₁ → x₁ x 

¬¬invol₂ : {X : Set} → ¬ ¬ ¬ X ↔ ¬ X
¬¬invol₂ = (λ x x₁ → x (λ x₂ → x₂ x₁)) , (λ x x₁ → x₁ x)

nnlem : {X : Set} → ¬ ¬ (X ⊎ ¬ X)
nnlem x = x (inr λ x₁ → x (inl x₁))

nndnp : {X : Set} → ¬ ¬ (¬ ¬ X → X)
nndnp = λ x → x (λ x₁ → exfalso (x₁ λ x₂ → x (λ x₃ → x₂)))

dec2stab : {X : Set} → (X ⊎ ¬ X) → (¬ ¬ X → X)
dec2stab (inl a) x₁ = a
dec2stab (inr b) x₁ = exfalso (x₁ b)

-- you have to decide:
{-
Dec : Set → Set
Dec A = A ⊎ ¬ A
-}

open import Lib.Dec.PatternSynonym

ee1 : {X Y : Set} → Dec (X ⊎ Y → ¬ ¬ (Y ⊎ X))
ee1 {X} {Y} = yes (λ x x₁ → x₁ (case x (λ x₂ → no x₂) (λ x₂ → yes x₂)))

ee2 : {X : Set} → Dec (¬ (X ⊎ ¬ X))
ee2 {X} = no λ x → x (no (λ x₁ → x (yes x₁)))

e3 : {X : Set} → Dec (¬ (X → (¬ X → X)))
e3 {X} = no (λ x → x (λ x₁ x₂ → x₁))

e4 : Dec ℕ
e4 = yes zero

e5 : Dec ⊥
e5 = no (λ x → x)

e6 : {X : Set} → Dec (⊥ → X ⊎ ¬ X)
e6 = yes (λ x → no (λ x₁ → x))

e7 : {X : Set} → Dec (X × ¬ X → ¬ X ⊎ X)
e7 = yes (λ {(fst₁ , snd₁) → yes snd₁})

e8 : {X : Set} → Dec ((X → X) → ⊥)
e8 = no (λ x → x (λ x₁ → x₁))

f1 : {X Y : Set} → ¬ ¬ X ⊎ ¬ ¬ Y → ¬ ¬ (X ⊎ Y)
f1 = λ {(yes a) x₁ → x₁ (yes (exfalso (a (λ x → x₁ (yes x)))))
      ; (no b) x₁ → x₁ (no (exfalso (b (λ x → x₁ (no x)))))}

f2 : ({X Y : Set} → ¬ (X × Y) → ¬ X ⊎ ¬ Y) → {X Y : Set} → ¬ ¬ (X ⊎ Y) → ¬ ¬ X ⊎ ¬ ¬ Y
f2 x {X} {Y} x₁ = x (λ x₂ → x₁ (λ x₃ → case x₃ (λ x₄ → fst x₂ x₄) (λ x₄ → snd x₂ x₄)))

-- Not exactly first order logic but kinda is.
notExists : ¬ ((X Y : Set) → X ⊎ Y → Y) 
notExists x with x X Y p1 
  where
    X : Set 
    X = ⊤ 
    Y : Set 
    Y = ⊥
    p1 :  X ⊎ Y
    p1 = yes tt
... | ()

f3 : Dec ((X Y : Set) → X ⊎ Y → Y)
f3 = no notExists

notExists2 : ¬ ((X Y Z : Set) → (X → Z) ⊎ (Y → Z) → (X ⊎ Y → Z)) 
notExists2 x with x X Y Z g1 h1
  where 
      X : Set 
      X = ⊤
      Y : Set 
      Y = ⊥
      Z : Set 
      Z = ⊥
      g1 : (X → Z) ⊎ (Y → Z)
      g1 = no (λ {()})
      h1 :  X ⊎ Y 
      h1 = yes tt
... | ()


f4 : Dec ((X Y Z : Set) → (X → Z) ⊎ (Y → Z) → (X ⊎ Y → Z))
f4 = no notExists2

f5 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f5 = yes (λ {X Y Z (x→z , y→z) → λ x → y→z (snd x)})

no6 : ¬ ((X Y Z : Set) → (X × Y → Z) → (X → Z) × (Y → Z)) 
no6 x with x X Y Z p1 
  where
      X : Set 
      X = ⊤
      Y : Set 
      Y = ⊥
      Z : Set 
      Z = ⊥
      p1 : X × Y → Z
      p1 ()
... | fst₁ , snd₁ = fst₁ tt

f6 : Dec ((X Y Z : Set) → (X × Y → Z) → (X → Z) × (Y → Z))
f6 = no no6

f7 : Dec ((X Y Z : Set) → (X ⊎ Y × Z) → (X ⊎ Y) × (X ⊎ Z))
f7 = yes (λ {X Y Z (yes a) → (yes a) , (yes a)
           ; X Y Z (no b) → (no (fst b)) , (no (snd b))})

no8 : ¬ ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → (X ⊎ Y) × Z)
no8 x with x X Y Z h1 
  where
      X : Set 
      X = ⊤
      Y : Set 
      Y = ⊥
      Z : Set 
      Z = ⊥
      h1 : (X ⊎ Y) × (X ⊎ Z)
      h1 = (yes tt) , (yes tt)
... | ()

f8 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → ((X ⊎ Y) × Z))
f8 = no no8
  --yes (λ X Y Z x → (fst x) , (case (snd x) (λ x₁ → {! inr (snd x)  !}) {!   !}))

f9 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → (X ⊎ Y × Z))
f9 = yes (λ {X Y Z (fst₁ , yes a) → yes a
           ; X Y Z (yes a , no b) → yes a
           ; X Y Z (no b₁ , no b) →  no (b₁ , b)})
   