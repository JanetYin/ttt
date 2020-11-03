module tut.t3.gy06 where

open import lib
open import numbers-and-bools

-- Pattern matching

--C-c C-c
_∧_ : Bool → Bool → Bool
true ∧ y = y
false ∧ y = false
--true ∧ true = true
--true ∧ false = false
--false ∧ true = false
--false ∧ false = false

--true ∧ y = y
--false ∧ y = false

--x ∧ y = if x then y else false
--_∧_ x y

--_∧_ = λ x y → if x then y else false

_∨_ : Bool → Bool → Bool
_∨_ = {!!}

-- Universe

_^3 : Set → Set
A ^3 = A × A × A

example : Bool ^3
example = true , false , true

ex2 : ℕ ^3
ex2 = 1 , 2 , 3

ex3 : (Bool ^3) ^3
ex3 = (true , false , false) , example , example

_^'_ : Set → ℕ → Set
A ^' zero = ⊤
A ^' suc n = A × A ^' n

-- ¬ : Set → Set
-- ¬ A = A → ⊥

Vec : Set → ℕ → Set
Vec = _^'_

tff tft : Vec Bool 3
tff = true , false , false , tt
tft = true , false , true , tt

5nums : Vec ℕ 5
5nums = {!!}

-- Dependent function space

-- we don't need abstract types anymore, we can say that something
-- works for every type:

-- sima fv: A → B
-- fuggo fv: (x : A) → B
--   (x : A  ) → B
ID : (A : Set) → A → A
ID = λ _ x → x

CONST : (A B : Set) → A → B → A
CONST = {!!}

comm× : (A B : Set) → (A × B) ↔ (B × A)
comm× = λ A B → (λ ab → proj₂ ab , proj₁ ab) , {!!}

-- Vectors
nil : (A : Set) → Vec A 0
nil = λ A → tt

cons : (A : Set)(n : ℕ) → A → Vec A n → Vec A (suc n)
cons A n x xs = x , xs 

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
