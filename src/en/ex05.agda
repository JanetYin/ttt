module en.ex05 where

open import Lib hiding (fromℕ ; minMax; _+∞_; coiteℕ∞; ∞)
open import Lib.Containers.Vector hiding (head; tail; map; length; _++_)
open import Lib.Containers.List hiding (head; tail; map; _++_; filter)

-- simple calculator (internally a number, you can ask for the number, add to that number, multiply that number, make it zero (reset))
record Machine : Set where
  coinductive
  field
    getNumber : ℕ
    add       : ℕ → Machine
    mul       : ℕ → Machine
    reset     : Machine
open Machine

calculatorFrom : ℕ → Machine
getNumber (calculatorFrom n) = n
add (calculatorFrom n) x = calculatorFrom (n + x)
mul (calculatorFrom n) = λ x → calculatorFrom (n * x)
reset (calculatorFrom n) = calculatorFrom 0

c0 c1 c2 c3 c4 c5 : Machine
c0 = calculatorFrom 0
c1 = add c0 3
c2 = add c1 5
c3 = mul c2 2
c4 = reset c3
c5 = add c4 2

-- TASK: Create a chocolate vending machine.
-- You can insert money into the machine (this should be ℕ, add this amount to our current credit).
-- The transaction can be canceled, the credit will be 0 and return our money.
-- We have 3 products, each costs a certain amount, and there are some in the machine initially.
-- + Twix: costs 350, initially 50 pieces in the machine.
-- + Croissant: costs 400, initially 75 pieces in the machine.
-- + Snickers: costs 375, initially 60 pieces in the machine.
-- We can buy 1 product if we have enough inserted money, in which case we should decrease the count of the item (if possible) and return the change, reset the credit to zero.
-- We can refill the machine, in this case, there should be 50 pieces of Twix, 75 of Croissant, and 60 of Snickers.

Price : Set
Price = ℕ

data Product : Set where
  Twix Croissant Snickers : Product

record CsokiAutomata : Set where
  coinductive
  field
      credit : ℕ
      add : ℕ → CsokiAutomata
      cancel : ℕ × CsokiAutomata
      twix : Price × ℕ
      -- the other two similarly
      buy : Product → ℕ × CsokiAutomata
      -- refill : ... this is just an activity, it only changes the state of the machine

-- Everything that needs to be in the machine's "memory" should be parameters in the constructor.
constructCsokiAutomata : (credit : ℕ) → (twix croissant snickers : Price × ℕ) → CsokiAutomata
constructCsokiAutomata n tw cr sn = {!!}

startCsokiAutomata : CsokiAutomata
startCsokiAutomata = constructCsokiAutomata 0 {!!} {!!} {!!} -- the three values for the three products specified in the task go here.
-----------------------------------------------------
-- conatural numbers
-----------------------------------------------------
{-
record ℕ∞ : Set where
  coinductive
  field
    pred∞ : Maybe ℕ∞
open ℕ∞
-}

0∞ : ℕ∞
pred∞ 0∞ = nothing

-- ∞ = \inf = \infty
1∞ : ℕ∞
pred∞ 1∞ = just 0∞

2∞ : ℕ∞
pred∞ 2∞ = just 1∞

∞ : ℕ∞
pred∞ ∞ = just ∞

_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
pred∞ (n +∞ k) with pred∞ n
pred∞ (n +∞ k) | nothing = pred∞ k
pred∞ (n +∞ k) | just x = just (x +∞ k)

-- This function exists to check the actual value of a conat.
-- The first parameter is the fuel, the maximum natural number it can return.
-- The second parameter is the conat we are interested in.
-- Naturally, the result is always nothing for ∞.
{-
ℕ∞→ℕ : ℕ → ℕ∞ → Maybe ℕ
ℕ∞→ℕ zero _ = nothing
ℕ∞→ℕ (suc n) c with pred∞ c
... | zero∞ = just 0
... | suc∞ b with ℕ∞→ℕ n b
... | nothing = nothing
... | just x = just (suc x)
-}

coiteℕ∞ : {B : Set} → (B → Maybe B) → B → ℕ∞
pred∞ (coiteℕ∞ f x) with f x
... | just n = just (coiteℕ∞ f n)
... | nothing = nothing

-- Vec and Fin
{-
infixr 5 _∷_
data Vec (A : Set) : ℕ → Set where
  [] : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

-- for data types, there are 2 built-in axioms
-- constructors are disjoint
-- the other is still a surprise :) (but guessable)
-}
head : {A : Set}{n : ℕ} → Vec A (suc n) → A
head {A} {n} (x ∷ xs) = x

tail : {A : Set}{n : ℕ} → Vec A (suc n) → Vec A n
tail (_ ∷ xs) = xs

countDownFrom : (n : ℕ) → Vec ℕ n
countDownFrom = {!!}

test-countDownFrom : countDownFrom 3 ≡ 3 ∷ 2 ∷ 1 ∷ []
test-countDownFrom = refl

infixr 5 _++_
_++_ : {A : Set}{k n : ℕ} → Vec A k → Vec A n → Vec A (k + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : ∀{i j}{A : Set i}{B : Set j}{n : ℕ} → (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

-- Which is the function that we still cannot write totally (yet)?
-- Indexing! It needs a new idea!

{-
data Fin : ℕ → Set where  -- Fin n = set with n elements
  fzero : {n : ℕ} → Fin (suc n)
  fsuc  : {n : ℕ} → Fin n → Fin (suc n)
-}

f0 : Fin 0 → ⊥
f0 ()

f1-0 : Fin 1
f1-0 = fzero {0}

f2-0 f2-1 : Fin 2
f2-0 = fzero {1}
f2-1 = fsuc {1} (fzero {0})

f3-0 f3-1 f3-2 : Fin 3
f3-0 = {!!}
f3-1 = {!!}
f3-2 = {!!}

f4-0 f4-1 f4-2 f4-3 : Fin 4
f4-0 = {!!}
f4-1 = {!!}
f4-2 = {!!}
f4-3 = {!!}

-- In Lib, the unicode ‼ is indexing.
infixl 9 _!!_
_!!_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A
(x ∷ xs) !! fzero = x
(x ∷ xs) !! fsuc n = xs !! n

test-!! : (the ℕ 3 ∷ 4 ∷ 1 ∷ []) !! (fsuc (fsuc fzero)) ≡ 1
test-!! = refl

test2-!! : (the ℕ 3 ∷ 4 ∷ 1 ∷ 0 ∷ 10 ∷ []) !! 3 ≡ 0 -- the literal 3 after !! is actually of type Fin 5.
test2-!! = refl

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ = {!!}

test-fromℕ : fromℕ 3 ≡ fsuc (fsuc (fsuc fzero))
test-fromℕ = refl

{-
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A
-}

{-
length : {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)
-}

fromList : {A : Set}(as : List A) → {!    !}
fromList = {!!}

tabulate : {n : ℕ}{A : Set} → (Fin n → A) → Vec A n
tabulate = {!!}

test-tabulate : tabulate (the (Fin 3 -> ℕ) (λ {fzero -> 6; (fsuc fzero) -> 9; (fsuc (fsuc fzero)) -> 2}))
                  ≡ 6 ∷ 9 ∷ 2 ∷ []
test-tabulate = refl

-- Sigma types

what : Σ ℕ (Vec Bool)
what = {!   !} , {!   !}

filter : {A : Set}{n : ℕ}(f : A → Bool) → Vec A n → Σ ℕ (Vec A) 
-- this can be refined, as there should never be more elements in it than n.
filter = {!   !}

test-filter : filter {ℕ} (3 <ᵇ_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ (2 , 4 ∷ 5 ∷ [])
test-filter = refl

smarterLengthList : ∀{i}{A : Set i}{n : ℕ} → List A → {!    !}
smarterLengthList = {!   !}

smarterLengthVec : ∀{i}{A : Set i}{n : ℕ} → Vec A n → {!    !}
smarterLengthVec = {!   !}

minMax' : ℕ → ℕ → ℕ × ℕ
minMax' n m = {!   !}

-- The same but much better, and mostly more precise.
-- In the previous version, I could return ugly things as well.
-- E.g., the constant (0 , 0).
minMax : (n m : ℕ) → Σ (ℕ × ℕ) (λ (a , b) → a ≤ℕ b × (n ≤ℕ m × n ≡ a × m ≡ b ⊎ m ≤ℕ n × n ≡ b × m ≡ a))
minMax n m = {!   !}
