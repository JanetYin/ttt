-- module Exam2 where

-- Max: 14 pont
--  0- 6: 1
--  7- 8: 2
--  8- 9: 3
-- 10-11: 4
-- 12-14: 5

-- bónusz: +2 pont, de nehéz!

----------------------------------------------------------------------
-- standard könyvtár
----------------------------------------------------------------------

-- üres típus

data ⊥ : Set where

-- egyenlőség

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a
infix 3 _≡_
{-# BUILTIN EQUALITY _≡_ #-}

cong : {A B : Set}(f : A → B){a a' : A} → a ≡ a' → f a ≡ f a'
cong f refl = refl

trans : {A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

-- természetes számok

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

_+_ : ℕ → ℕ → ℕ
zero + b = b
suc a + b = suc (a + b)

{-# BUILTIN NATURAL ℕ #-}

-- kételemű halmaz

data Bool :  Set where
  true false : Bool

-- lista

data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A)(xs : List A) → List A

infixr 5 _∷_

-- diszjunkt unió

data _⊎_ (A B : Set) : Set where
  inl : A  → A ⊎ B
  inr : B  → A ⊎ B

infixr 3 _⊎_

-- Descartes-szorzat

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _×_
infixr 6 _,_

-- függő pár

data Σ (A : Set)(B : A → Set) : Set where
  _,_ : (a : A) → B a → Σ A B

----------------------------------------------------------------------
-- két lemma (2)
----------------------------------------------------------------------

lem1 : ∀{A B} → (A × B → ⊥) → (A → B → ⊥)
lem1 x x₁ x₂ = x (x₁ , x₂)

lem2 : ∀{A B} → (A → B → ⊥) → (A × B → ⊥)
lem2 x (a , b) = x a b

----------------------------------------------------------------------
-- logikai műveletek és egy tulajdonsága (3)
----------------------------------------------------------------------

-- definiáljuk a logikai negációt, és ill. vagy műveletet

neg : Bool → Bool
neg true = false
neg false = true

_&&_ : Bool → Bool → Bool
true && true = true
true && false = false
false && b = false

T&& : true && false ≡ false
T&& = refl

_||_ : Bool → Bool → Bool
true || b = true
false || b = b

Tneg&&|| : neg (false && true) || (false || false) ≡ true
Tneg&&|| = refl

-- bizonyítsuk be az alábbi lemmát

lem3 : ∀ (x y : Bool) → neg (x && y) ≡ neg x || neg y
lem3 true true = refl
lem3 true false = refl
lem3 false true = refl
lem3 false false = refl

----------------------------------------------------------------------
-- összehasonlítás (2)
----------------------------------------------------------------------

_>2 : ℕ → Bool
zero >2 = false
suc zero >2 = false
suc (suc zero) >2 = false
suc (suc (suc x)) >2 = true

1>2 : 1 >2 ≡ false
1>2 = refl

2>2 : 2 >2 ≡ false
2>2 = refl

3>2 : 3 >2 ≡ true
3>2 = refl

4>2 : 4 >2 ≡ true
4>2 = refl

lem4 : (n : ℕ) → (3 + n) >2 ≡ true
lem4 n = refl

lem5 : false ≡ true → ⊥
lem5 ()

lem6 : ((n : ℕ) → (2 + n) >2 ≡ true) → ⊥
lem6 f with f zero
...| y = lem5 y

----------------------------------------------------------------------
-- három függvény (3)
----------------------------------------------------------------------

f : ∀{A B} → ((A ⊎ (A → B)) → B) → B
f g = g (inr (λ x → g (inl x)))

g : ∀{A B C} → (A → C) × (B → C) → ((A ⊎ B) → C)
g (x₁ , x₂) (inl x) = x₁ x
g (x₁ , x₂) (inr x) = x₂ x

h : ∀{A B C} → ((A ⊎ B) → C) → (A → C) × (B → C)
h {A} {B} {C} f₁ = (λ x → f₁ (inl x)) , (λ x → f₁ (inr x))

----------------------------------------------------------------------
-- egy nemkommutatív monoid ℕ-en (4)
----------------------------------------------------------------------

j : ℕ → ℕ → ℕ
j zero n = n
j (suc m) n = suc m

-- bizonyítsuk be az alábbi tulajdonságokat!

j-leftzero : ∀ n → j n 0 ≡ n
j-leftzero zero = refl
j-leftzero (suc n) = cong suc refl

j-rightzero : ∀ n → n ≡ j n 0
j-rightzero zero = refl
j-rightzero (suc n) = refl

j-assoc : ∀ n m l → j n (j m l) ≡ j (j n m) l
j-assoc zero m l = refl
j-assoc (suc n) m l = refl

j-noncomm : Σ ℕ λ x → Σ ℕ λ y → j x y ≡ j y x → ⊥
j-noncomm = suc (suc zero) , (suc zero , λ {()})

----------------------------------------------------------------------
-- bónusz
----------------------------------------------------------------------
f1 : Bool → Bool 
f1 true = false
f1 false = true

f2 : Bool → Bool 
f2 x = x 



sym : ∀{A}{a b : A} → a ≡ b → b ≡ a
sym refl = refl

bool3 : (f : Bool → Bool)(x : Bool) → f (f (f x)) ≡ f x
bool3 f true with f true in eq1 | f false in eq2
bool3 f true | true | _ = trans (cong f eq1) eq1
bool3 f true | false | true = {!   !}
bool3 f true | false | false = {!   !}
bool3 f false with f true in eq1 | f false in eq2
bool3 f false | true | _ = {!   !}
bool3 f false | false | true = {!   !}
bool3 f false | false | false = {!   !}

-- with  f (f x)
-- bool3 f true | true = refl
-- bool3 f true | false = sym {!   !}
-- -- bool3 f false | true = {!  !}
-- bool3 f false | true = {!   !}
-- bool3 f false | false = refl
--     where 
--         f3 : Bool → Bool 
--         f3 x = true 
--         f4 : Bool → Bool 
--         f4 x = false 




-- f2 
{-
f1 b → b 

-}
  