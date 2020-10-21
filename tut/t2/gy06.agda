module tut.t2.gy06 where

open import lib
open import numbers-and-bools

-- Pattern matching

_∧_ : Bool → Bool → Bool
_∧_ = {!!}

_∨_ : Bool → Bool → Bool
_∨_ = {!!}

-- Universe

_^3 : Set → Set
A ^3 = {!!}

_^'_ : Set → ℕ → Set
_^'_ = {!!}

Vec : Set → ℕ → Set
Vec = _^'_

tff tft : Vec Bool 3
tff = {!!}
tft = {!!}

5nums : Vec ℕ 5
5nums = {!!}

-- Dependent function space

-- we don't need abstract types anymore, we can say that something
-- works for every type:

ID : (A : Set) → A → A
ID = {!!}

CONST : (A B : Set) → A → B → A
CONST = {!!}

comm× : (A B : Set) → (A × B) ↔ (B × A)
comm× = {!!}

-- Vectors
nil : (A : Set) → Vec A 0
nil = {!!}

cons : (A : Set)(n : ℕ) → A → Vec A n → Vec A (suc n)
cons = {!!}

head : (A : Set)(n : ℕ) → Vec A (suc n) → A
head = {!!}

tail : (A : Set)(n : ℕ) → Vec A (suc n) → Vec A n
tail = {!!}

--numbers n = [n - 1, n - 2, ... , 0]
numbers : (n : ℕ) → Vec ℕ n
numbers = {!!}

count : (A : Set)(n : ℕ) → A → Vec A n → ℕ
count = {!!}

isEmpty : (A : Set)(n : ℕ) → A → Vec A n → Bool
isEmpty = {!!}

-- Equality

Eqb : Bool → Bool → Set
Eqb = {!!}

true=true : Eqb true true
true=true = {!!}

¬true=false : ¬ Eqb true false
¬true=false = {!!}

-- now we can write unit tests inside Agda:

testNot1 : Eqb (not (not false)) false
testNot1 = {!!}

testAnd1 : Eqb (and true false) false
testAnd1 = {!!}

testAnd2 : Eqb (and true true) true
testAnd2 = {!!}

toSet : Bool → Set
toSet = {!!}

Eqn : ℕ → ℕ → Set
Eqn = λ x y → toSet (eq x y)

test+1 : Eqn (3 + 2) 5
test+1 = {!!}

test+2 : ¬ Eqn (3 + 2) 4
test+2 = {!!}

eqVec : (l : ℕ) → Vec ℕ l → Vec ℕ l → Bool
eqVec = {!!}

EqVec : (l : ℕ) → Vec ℕ l → Vec ℕ l → Set
EqVec = {!!} 

-- Now we can test our Vec functions
-- Test: head, tail, cons, nil, numbers, etc...

-- More vectors
map : (A B : Set)(n : ℕ)(f : A → B) → Vec A n → Vec B n
map = {!!}

foldl : (A B : Set)(n : ℕ) → A → Vec B n → A
foldl = {!!}

foldr : (A B : Set)(n : ℕ) → B → Vec A n → B
foldr = {!!}

-- etc...
-- write tests
