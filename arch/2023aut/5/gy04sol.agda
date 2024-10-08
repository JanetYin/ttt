open import Lib hiding (_+∞_; coiteℕ∞; ℕ∞→ℕ)

open import Lib.Containers.List hiding (zipWith; head; tail)
open import Lib.Containers.Stream hiding (zipWith; coiteStream)

---------------------------------------------------------
-- positivity (vizsgán nem kell)
---------------------------------------------------------

{-# NO_POSITIVITY_CHECK #-}
data Tm : Set where
  lam : (Tm → Tm) → Tm

app : Tm → (Tm → Tm)
app = {!!}

self-apply : Tm
self-apply = lam (λ t → app t t)

-- C-c C-n this:
Ω : Tm
Ω = app self-apply self-apply

{-# NO_POSITIVITY_CHECK #-}
data Weird : Set where
  foo : (Weird → ⊥) → Weird

noweird : Weird → ⊥
noweird (foo x) = x (foo x)

weird : Weird
weird = foo noweird

bad : ⊥
bad = noweird weird

{-
Positivity checking rules out datatypes such as Weird. In general, the (strict) positivity criterion says that each constructor c of a datatype D should have a type of the form

c : (x1 : A1)(x2 : A2) ... (xn : An) → D xs

where the type Ai of each argument is either non-recursive (i.e. it doesn't refer to D) or of the form (y1 : B1)(y2 : B2) ... (ym : Bm) → D ys where each Bj doesn't refer to D. 
-}

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

-- an infinite list filled with zeroes:
-- zeroesList : List ℕ
-- zeroesList = 0 ∷ zeroesList       -- ∷ is \::

-- now with a stream:
zeroes : Stream ℕ
head zeroes = 0
tail zeroes = zeroes

{-
Coinduction is the mathematical dual to structural induction. Coinductively defined types are known as codata and are typically infinite data structures, such as streams.
As a definition or specification, coinduction describes how an object may be "observed", "broken down" or "destructed" into simpler objects.
-}

-- by pattern match on n
-- [n,n-1,...,0]
countDownFrom : ℕ → List ℕ
countDownFrom zero = []
countDownFrom (suc n) = suc n ∷ (countDownFrom n)

-- [n,n+1,...]
-- fromList : ℕ -> List ℕ
-- fromList n = n ∷ (fromList (suc n))

-- from n is not by pattern match on n
from : ℕ → Stream ℕ
head (from n) = n
tail (from n) = from (suc n)

-- pointwise addition
zipWith : {A B C : Set} → (A → B → C) → Stream A → Stream B → Stream C
head (zipWith f as bs) = f (head as) (head bs)
tail (zipWith f as bs) = zipWith f (tail as) (tail bs)

filterL : {A : Set} → (A → Bool) → List A → List A
filterL p [] = []
filterL p (x ∷ xs) = if p x then x ∷ filterL p xs else filterL p xs

-- this cannot be defined:
-- filterS : {A : Set} → (A → Bool) → Stream A → Stream A
-- head (filterS p xs) = if p (head xs) then head xs else head (filterS p (tail xs))
-- tail (filterS p xs) = {!!}

-- one element from the first stream, then from the second stream, then from the first, and so on
-- házi
interleave : {A : Set} → Stream A → Stream A → Stream A
interleave = {!!}

-- get the n^th element of the stream
get : {A : Set} → ℕ → Stream A → A
get zero xs = head xs
get (suc n) xs = get n (tail xs)

-- the first stream contains the indices
-- byIndices [0,2,3,2,...] [1,2,3,4,5,...] = [1,3,4,3,...]
-- házi
-- byIndices : {A : Set} → Stream ℕ → Stream A → Stream A
-- byIndices = {!!}

-- iteℕ : (A : Set) → A → (A → A)  → ℕ → A
--        \______________________/
--         ℕ - algebra

coiteStream : {A : Set} (B : Set) → (B → A) → (B → B) → B → Stream A
--                       \____________________________/
--                        Stream A - coalgebra
head (coiteStream B h t b) = h b
tail (coiteStream B h t b) = coiteStream B h t (t b)

-- ex: redefine the above functions using coiteStream

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
add (calculatorFrom n) m = calculatorFrom (n + m)
mul (calculatorFrom n) m = calculatorFrom (n * m)
reset (calculatorFrom n) = calculatorFrom 0

c0 c1 c2 c3 c4 c5 : Machine
c0 = calculatorFrom 0
c1 = add c0 3
c2 = add c1 5
c3 = mul c2 2
c4 = reset c3
c5 = add c4 2

-- conatural numbers
{-
record ℕ∞ : Set where          -- ∞ is \inf
  coinductive
  field
    pred∞ : Maybe ℕ∞
open ℕ∞
-}

co0 co1 : ℕ∞
pred∞ co0 = nothing
pred∞ co1 = just co0

{-
∞ : ℕ∞
pred∞ ∞ = just ∞
-}

{-
_+∞_ : ℕ∞ -> ℕ∞ -> ℕ∞     -- \bN \inf
(n +∞ m) with (pred∞ n)
(n +∞ m) | nothing = m
(n +∞ m) | just n-1 = suc∞ (n-1 +∞ m)
  where
  suc∞ : ℕ∞ -> ℕ∞
  pred∞ (suc∞ n) = just n
-}

_+∞_ : ℕ∞ -> ℕ∞ -> ℕ∞
pred∞ (n +∞ m) with pred∞ n
... | just n-1 = just (n-1 +∞ m)
... | nothing = pred∞ m

-- Ez a függvény létezik a Libben; ezzel lehet megnézni
-- egy conat tényleges értékét.
-- Az első paraméter a fuel, ennél kisebbet tud csak visszaadni.
-- Második paraméter a conat, amire kíváncsiak vagyunk.
-- Értelemszerűen ∞-re mindig nothing az eredmény.
ℕ∞→ℕ : ℕ → ℕ∞ → Maybe ℕ
ℕ∞→ℕ zero _ = nothing
ℕ∞→ℕ (suc n) c with pred∞ c
ℕ∞→ℕ (suc n) c | nothing = just zero
ℕ∞→ℕ (suc n) c | just c-1 with ℕ∞→ℕ n c-1
ℕ∞→ℕ (suc n) c | just c-1 | just x = just (suc x)
ℕ∞→ℕ (suc n) c | just c-1 | nothing = nothing

-- ℕ∞→ℕ 4 co2 = just 2
-- ℕ∞→ℕ 4 co3 = just 3
-- ℕ∞→ℕ 4 co4 = nothing
-- ℕ∞→ℕ 4 ∞   = nothing

coiteℕ∞ : {B : Set} → (B → Maybe B) → B → ℕ∞
coiteℕ∞ f b = {!!}

-- TODO, further exercises: network protocols, simple machines: chocolate machine (input: coin, getChocolate, getBackCoins, output: error, chocolate, money back), some Turing machines, animations, IO, repl, shell
