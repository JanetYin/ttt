module en.ex04 where

open import Lib hiding (_+∞_; coiteℕ∞;add)

open import Lib.Containers.List hiding (zipWith; head; tail; length; map; _++_; iteList; take)
open import Lib.Containers.Stream hiding (zipWith; coiteStream; map; _++_)

---------------------------------------------------------
-- η rules for types
---------------------------------------------------------
{-
Reminder: The η-rule tells us what to do when applying a constructor to a destructor.
For example, for functions, (λ a → f a) ≡ f, where function application is the destructor and λ is the constructor.

Naturally, other types also have η-rules.

Let's take ⊤ as an example:
Destructor: ite⊤ : A → ⊤ → A

Based on this, the η-rule will be:
ite⊤ tt ≡ λ x → x

This can, of course, be proven in Agda.
-}

ite⊤ : ∀{i}{A : Set i} → A → ⊤ → A
ite⊤ x _ = x

⊤η : ∀{x} → ite⊤ tt x ≡ x
⊤η = refl

{-
As you remember, the η-rule for ⊤ looks like ∀ a → a ≡ tt,
so it will also be true here that a type can have multiple equivalent η-rules.

Let's look again at the Bool type. Its β-rules were:
if false then u else v ≡ u
if true then u else v ≡ v

What could be the η-rule? How can we "apply a constructor to a destructor" in this case?
For if_then_else_, the "then" and "else" branches can have arbitrary values;
we can even write a constructor here. So we can construct the η-rules by writing the constructors of the same type into the appropriate places of the destructor.
For Bool, this means that in if_then_else_, we need to write the two constructors of Bool into the second and third positions.
Furthermore, we need to write the two constructors in such a way that we essentially get the "identity" function on the given type.
For Bool, this means we need to parameterize if_then_else_ such that the result is false for false, and true for true.

Based on this, what will be a possible η-rule for Bools?
Answer: if_then_true_else_false = λ b → b

The same can be done with the known 𝟛 type.
data 𝟛 : Set where
  a1 a2 a3 : 𝟛

The destructor is known: ite𝟛 : A → A → A → 𝟛 → A

What will be the η-rule for 𝟛?
Answer: ite𝟛 a1 a2 a3 ≡ λ b → b

For natural numbers, the situation is also unchanged.
The destructor is known: iteℕ : A → (A → A) → ℕ → A

What will be the η-rule for ℕ?
Answer: iteℕ zero suc ≡ λ n → n
-}

---------------------------------------------------------
-- positivity
---------------------------------------------------------

-- Why does Agda not allow defining certain types? For example, by default, the following is also not allowed.

{-# NO_POSITIVITY_CHECK #-}
data Tm : Set where
  lam : (Tm → Tm) → Tm

-- TASK: Return the value of lam from Tm.
app : Tm → (Tm → Tm)
app (lam x) = x

self-apply : Tm
self-apply = lam λ x → app x x

-- From lambda calculus: Y = (λ x → x x) (λ x → x x)
-- C-c C-n this:
Ω : Tm
Ω = app self-apply self-apply

{-# NO_POSITIVITY_CHECK #-}
data Weird : Set where
  foo : (Weird → ⊥) → Weird
  -- How to read the "foo" constructor in Hungarian?
  -- If Weird has no elements, then it has an element.
unweird : Weird → ⊥
unweird (foo x) = x (foo x)

-- There MUST NOT be a value of type ⊥, otherwise the system is inconsistent and unusable for ANYTHING.
bad : ⊥
bad = unweird (foo unweird)

pr : ⊥ ≡ Bool
pr = exfalso bad

---------------------------------------------------------
-- lists
---------------------------------------------------------

{-
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A
infixr 5 _∷_
-}

-- TASK: Determine the number of elements in a list!
length : {A : Set} → List A → ℕ
length [] = 0
length (_ ∷ xs) = suc (length xs)

length-test1 : length {ℕ} (1 ∷ 2 ∷ 3 ∷ []) ≡ 3
length-test1 = refl
length-test2 : length {ℕ} (1 ∷ []) ≡ 1
length-test2 = refl

-- TASK: Sum the numbers in a list.
sumList : List ℕ → ℕ
sumList [] = 0
sumList (x ∷ xs) = x + sumList xs

sumList-test : sumList (1 ∷ 2 ∷ 3 ∷ []) ≡ 6
sumList-test = refl

-- TASK: Concatenate two lists!
_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys
infixr 5 _++_

++-test : the (List ℕ) (3 ∷ 2 ∷ []) ++ the (List ℕ) (1 ∷ 4 ∷ []) ≡ 3 ∷ 2 ∷ 1 ∷ 4 ∷ []
++-test = refl

-- TASK: Apply a function to every element in a list!
map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

map-test : map (_+ 2) (3 ∷ 9 ∷ []) ≡ (5 ∷ 11 ∷ [])
map-test = refl

-- TASK: Define the list eliminator! Process a list:
-- if the list is empty, just return a base value
-- if the list has elements, apply a function to it with the base value right-associated.
-- In Haskell, foldr
-- How many parameters will the function have?
iteList : {A B : Set} → B → (A → B → B) → List A → B
iteList b f [] = b
iteList b f (x ∷ xs) = f x (iteList b f xs)
{-
iteList-test1 : iteList 3 _^_ (2 ∷ 3 ∷ []) ≡ 2 ^ 27
iteList-test1 = refl
-}

iteList-test2 : iteList {ℕ} [] _∷_ (1 ∷ 2 ∷ 3 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ []
iteList-test2 = refl

-- TASK: define the above functions (length, ..., map) using iteList!

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

-- This type essentially encodes infinite lists.
-- Finite lists are not included, only infinite ones!


-- Copattern matching!
-- TASK: Define the infinite list consisting only of zeros.
zeroes : Stream ℕ
head zeroes = 0
tail zeroes = zeroes
-- How does Agda know this is total?
-- The termination checker cannot run since the list is infinite.
-- Productivity checker

-- by pattern match on n
-- TASK: Define the list that counts down from n to 1 one by one.
countDownFrom : ℕ → List ℕ
countDownFrom zero = []
countDownFrom (suc n) = suc n ∷ countDownFrom n

-- from n is not by pattern match on n
-- copattern match on Stream
-- TASK: Define the infinite list that counts up from n one by one!
from : ℕ → Stream ℕ
head (from n) = n
tail (from n) = from (suc n)

-- pointwise addition
zipWith : {A B C : Set} → (A → B → C) → Stream A → Stream B → Stream C
head (zipWith f xs ys) = f (head xs) (head ys)
tail (zipWith f xs ys) = zipWith f (tail xs) (tail ys)

-- Can filter be defined on simple lists?
filterL : {A : Set} → (A → Bool) → List A → List A
filterL p [] = []
filterL p (x ∷ xs) = let r = filterL p xs in if p x then x ∷ r else r

-- Can filter be defined on Streams?
-- No
{-
filterS : {A : Set} → (A → Bool) → Stream A → Stream A
head (filterS p xs) = if p (head xs) then head xs else head (filterS p (tail xs))
                                                       ^^^^ -- not consumed destructor
tail (filterS p xs) = {!!}
-}
-- one element from the first stream, then from the second stream, then from the first, and so on
interleave : {A : Set} → Stream A → Stream A → Stream A
head (interleave xs ys) = head xs
tail (interleave xs ys) = interleave ys (tail xs)

{-
interleave : {A : Set} → Stream A → Stream A → Stream A
head (interleave xs ys) = head xs
head (tail (interleave xs ys)) = head ys
tail (tail (interleave xs ys)) = interleave (tail xs) (tail ys)
-}
-- get the n^th element of the stream
get : {A : Set} → ℕ → Stream A → A
get zero xs = head xs
get (suc n) xs = get n (tail xs)

-- byIndices [0,2,3,2,...] [1,2,3,4,5,...] = [1,3,4,2,...]
byIndices : {A : Set} → Stream ℕ → Stream A → Stream A
byIndices x x₁ = {!   !}

-- iteℕ : (A : Set) → A → (A → A)  → ℕ → A
--        \______________________/
--         ℕ - algebra

-- head : Stream A → A
-- tail : Stream A → Stream A
-- What will be the constructor for Stream?
coiteStream : {A B : Set} → (B → A) → (B → B) → B → Stream A
--               \______________________________/
--                        Stream A - coalgebra
head (coiteStream h t s) = h s
tail (coiteStream h t s) = coiteStream h t (t s)

-- ex: redefine the above functions using coiteStream

-- Based on the description at the top of the file, the η-rule can naturally be given for Stream as well.
-- Note: Due to type-theoretical "issues," this will be an unprovable statement in MLTT.
-- (It holds, but MLTT is incapable of proving it, as evidenced by the fact that it cannot be proven or disproven.)
Stream-η : {A : Set}(s : Stream A) → coiteStream head tail s ≈S s
head-≡ (Stream-η s) = refl
tail-≈ (Stream-η s) = Stream-η (tail s)

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

-- TASK: Create a chocolate vending machine.
-- You can insert money into the machine (this should be ℕ, add this amount to our current credit).
-- The transaction can be canceled, the credit will be 0 and return our money.
-- We have 3 products, each costs a certain amount, and there are some in the machine initially.
-- + Twix: costs 350, initially 50 pieces in the machine.
-- + Croissant: costs 400, initially 75 pieces in the machine.
-- + Snickers: costs 375, initially 60 pieces in the machine.
-- We can buy 1 product if we have enough inserted money, in which case we should decrease the count of the item (if possible) and return the change, reset the credit to zero.
-- We can refill the machine, in this case, there should be 50 pieces of Twix, 75 of Croissant, and 60 of Snickers.

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

_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
_+∞_ = {!!}

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
coiteℕ∞ = {!!}

-- TODO, further exercises: network protocols, simple machines: chocolate machine (input: coin, getChocolate, getBackCoins, output: error, chocolate, money back), some Turing machines, animations, IO, repl, shell
