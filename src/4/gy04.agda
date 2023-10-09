open import Lib hiding (_+∞_; coiteℕ∞)

open import Lib.Containers.List hiding (zipWith; head; tail)
open import Lib.Containers.Stream hiding (zipWith; coiteStream)

---------------------------------------------------------
-- positivity
---------------------------------------------------------

{-# NO_POSITIVITY_CHECK #-}
data Tm : Set where
  lam : (Tm → Tm) → Tm

app : Tm → (Tm → Tm)
app (lam x) x₁ = x x₁

self-apply : Tm
self-apply = lam (λ t → app t t)

-- C-c C-n this:
Ω : Tm
Ω = app self-apply self-apply

{-# NO_POSITIVITY_CHECK #-}
data Weird : Set where
  foo : (Weird → ⊥) → Weird

unweird : Weird → ⊥
unweird (foo x) = x (foo x)

bad : ⊥
bad = unweird (foo unweird)

---------------------------------------------------------
-- coinductive types
---------------------------------------------------------

{-
record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream
-}
-- check that the type of head : Stream A → A
--                        tail : Stream A → Stream A

zeroes : Stream ℕ
head zeroes = zero
tail zeroes = zeroes

-- by pattern match on n
countDownFrom : ℕ → List ℕ
countDownFrom zero = zero ∷ []
countDownFrom (suc n) = suc n ∷ countDownFrom n

-- from n is not by pattern match on n
from : ℕ → Stream ℕ
head (from n) = n
tail (from n) = from (suc n)

-- pointwise addition
zipWith : {A B C : Set} → (A → B → C) → Stream A → Stream B → Stream C
head (zipWith x x₁ x₂) = x (head x₁) (head x₂)
tail (zipWith x x₁ x₂) = zipWith x (tail x₁) (tail x₂)

filterL : {A : Set} → (A → Bool) → List A → List A
filterL = {!!}

-- this cannot be defined:
-- filterS : {A : Set} → (A → Bool) → Stream A → Stream A
-- filterS P xs = ?

-- one element from the first stream, then from the second stream, then from the first, and so on
interleave : {A : Set} → Stream A → Stream A → Stream A
head (interleave x x₁) = head x
head (tail (interleave x x₁)) = head x₁
tail (tail (interleave x x₁)) = interleave (tail x) (tail x₁)

-- get the n^th element of the stream
get : {A : Set} → ℕ → Stream A → A
get zero x = head x
get (suc n) x = get n (tail x)

-- byIndices [0,2,3,2,...] [1,2,3,4,5,...] = [1,3,4,3,...]
byIndices : {A : Set} → Stream ℕ → Stream A → Stream A
byIndices = {!!}

-- iteℕ : (A : Set) → A → (A → A)  → ℕ → A
--        \______________________/
--         ℕ - algebra

coiteStream : {A : Set} (B : Set) → (B → A) → (B → B) → B → Stream A
--                       \____________________________/
--                        Stream A - coalgebra
head (coiteStream B h t b) = h b
tail (coiteStream B h t b) = coiteStream B h t (t b)

-- ex: redefine the above functions using coiteStream



-- ex: look at conatural numbers in Thorsten's book and do the exercises about them

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
calculatorFrom n = {!!}

c0 c1 c2 c3 c4 c5 : Machine
c0 = calculatorFrom 0
c1 = add c0 3
c2 = add c1 5
c3 = mul c2 2
c4 = reset c3
c5 = add c4 2

-- conatural numbers
{-
record ℕ∞ : Set where
  coinductive
  field
    pred∞ : Maybe ℕ∞
open ℕ∞
-}

_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
pred∞ (x +∞ x₁) with (pred∞ x)
... | just x₂ = just (x₂ +∞ x₁)
... | nothing = just x₁

-- Ez a függvény létezik, ezzel lehet megnézni
-- egy conat tényleges értékét.
-- Az első paraméter a fuel, maximum ezt a természetes számot tudja visszaadni.
-- Második paraméter a conat, amire kíváncsiak vagyunk.
-- Értelemszerűen ∞-re mindig nothing az eredmény.
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
pred∞ (coiteℕ∞ x x₁) with x x₁ 
... | just x₂ = just (coiteℕ∞ x x₂)
... | nothing = nothing

-- TODO, further exercises: network protocols, simple machines: chocolate machine (input: coin, getChocolate, getBackCoins, output: error, chocolate, money back), some Turing machines, animations, IO, repl, shell
