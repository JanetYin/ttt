module en.ex03 where

open import Lib hiding (_+_; _*_; _-_; _^_; _!; pred; pred'; _>_; _<_; min; max)
open import Lib.Containers.List hiding (length; _++_; map; iteList)

-- η = \eta = \Gh

--------------------------------------------------------
-- β, η rules simply explained
--------------------------------------------------------
{-
The β-rules essentially define how to compute with my values; 
that is, what to do when applying a destructor to a constructor.
For example, for functions, (λ n → n + 2) 3, in this expression, the λ is the constructor,
 the function application is the destructor; in this case, you just need to substitute the value in the appropriate place, 
 then compute its value.

The η-rules define what to do when applying a constructor to a destructor.
For example, for functions, (λ x → (1 + _) x), in this the lambda contains a function application, 
which we mentioned earlier is a destructor; the λ is the constructor, and specifically for functions, 
we know that the λ can be omitted along with the passed x (λ x → (1 + _) x) ≡ (1 + _).
-}

--------------------------------------------------------
-- types β rules
--------------------------------------------------------
{-
Every type can have its β rules defined based on the type.

β-rules specify what to do with a given value of a type to distinguish it from other values of the type.

This idea is easier to illustrate with Bool:

data Bool : Set where
  false true : Bool

How can we distinguish false from true?
We need a function (destructor) that yields different results for different Bool values syntactically 
and handles ONLY and EXACTLY the values of Bool, so since Bool has two values, 
the destructor must handle EXACTLY two elements, no more, no less.

Which function over Bools gives clearly distinct results for false and true? 
(This is known from Haskell or other OOP languages.)
What is its destructor?
Answer: if_then_else_

How many β-rules are needed for Bool?
Answer: 2

What will these β-rules be?
Answer:
if false then u else v ≡ v
if true then u else v ≡ u
---------------------------------------------------------
If we write a type with 3 elements (essentially just an enum):

data 𝟛 : Set where
  a1 a2 a3 : 𝟛

What will be the destructor for the type 𝟛?
Answer: ite𝟛 : A → A → A → 𝟛 → A

Then what will be the β-rules for this type?
Answer:
ite𝟛 a b c a1 ≡ a
ite𝟛 a b c a2 ≡ b
ite𝟛 a b c a3 ≡ c

ite𝟛 : {A : Set} → A → A → A → 𝟛 → A
ite𝟛 a b c a1 = a
ite𝟛 a b c a2 = b
ite𝟛 a b c a3 = c
----
For 4 elements:

data 𝟜 : Set where
  b1 b2 b3 b4 : 𝟜

What will be its destructor?
Answer: ite𝟜

What will be its β-rules?
Answer:
ite𝟜 a b c d a1 ≡ a
ite𝟜 a b c d a2 ≡ b
ite𝟜 a b c d a3 ≡ c
ite𝟜 a b c d a4 ≡ d
----
What is the destructor for the ⊤ type?
Answer:  ite⊤ : A → ⊤ → A

What will be the β-rule for the ⊤ type?
Answer:
ite𝟜 a tt ≡ a
----
What is the destructor for ⊥?
Answer: exfalso

What will be the β-rule for the ⊥ type?

Answer:  exfalso : ∀{i}{A : Set i} → ⊥ → A
----------------------------------------------------------
What happens if the types have parameters?

data Apple : Set where
  c1 : Apple
  c2 : Bool → Apple

Naturally, nothing special, the destructor will include exactly the same constructors as before.

What will be its destructor?
Answer: iteApple : A → (Bool → A) → Apple → A

What will be its β-rules?
Answer:
iteApple a f c1 ≡ a
iteApple a f (c2 true) ≡ f true
iteApple a f (c2 false) ≡ f false
-----------------------------------------------------------
What happens if a constructor has at least two parameters?

For example, an ordered pair: _,_ : A → B → A × B

Nothing, the destructor can still be generated the same way (this does not mean it is the only good one).
What will be a destructor for ordered pairs?

The one generated based on the above: uncurry : (A → B → C) → A × B → C

Other destructors are also valid, for example, the following two together:
- fst : A × B → A
- snd : A × B → B

What are the β-rules based on these?
With uncurry, only one rule is needed: uncurry f (a , b) ≡ f a b
With fst, snd, two rules are needed (since there are two destructors for one constructor, 2 ∙ 1 = 2): 
  fst (a , b) ≡ a; snd (a , b) ≡ b
------------------------------------------------------------
data Pear : Set where
  d1 : Pear
  d2 : Bool → Pear
  d3 : Bool → 𝟛 → Pear

What will be the destructor for this type?
Answer:
itePear : C → (Bool → C) → (Bool → 𝟛 → C) → Pear → C 


And its β-rules?
Answer:
itePear a f f₁ c1 ≡ a
itePear a f f₁ (c2 true) ≡ f true
itePear a f f₁ (c2 false) ≡ f false
itePear a f f₁ (c3 true a1) ≡ f₁ true a1
itePear a f f₁ (c3 true a2) ≡ f₁ true a2
itePear a f f₁ (c3 true a3) ≡ f₁ true a3
itePear a f f₁ (c3 false a1) ≡ f₁ false a1
itePear a f f₁ (c3 false a2) ≡ f₁ false a2
itePear a f f₁ (c3 false a3) ≡ f₁ false a3
-}

---------------------------------------------------------
-- η rules for types
---------------------------------------------------------
-- This will be included at the beginning of the next practice session, there is plenty to do here already.

---------------------------------------------------------
-- natural numbers, no cheating anymore
---------------------------------------------------------

-- Natural numbers are defined as known from discrete mathematics,
-- so we have 0 and its successor.
{-
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
-}

-- 2 = suc (suc zero)
-- Maybe type known from Haskell.
{-
data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A
-}

-- TASK: Decrease a given natural number by one if possible.
pred' : ℕ → Maybe ℕ
pred' zero = nothing
pred' (suc n) = just n

-- TASK: If possible, add one to the number, otherwise the result should be 0.
zerosuc : Maybe ℕ → ℕ
zerosuc (just x) = suc x
zerosuc nothing = 0

pred↔zerosuc-test1 : pred' (zerosuc nothing) ≡ nothing
pred↔zerosuc-test1 = refl
pred↔zerosuc-test2 : {n : ℕ} → pred' (zerosuc (just n)) ≡ just n
pred↔zerosuc-test2 = refl

-- Ugly pred, because it does not do what it should mathematically, 0 has no predecessor, it cannot be 0.
pred'' : ℕ → ℕ
pred'' zero = zero
pred'' (suc n) = n

-- A much better pred can be provided; it can be done without Maybe.
-- This is the direction the subject is heading; precise specification is important!
-- We need a function that returns a type.
-- Then the proper pred.

NotZero? : ℕ → Set
NotZero? zero = ⊥
NotZero? (suc n) = ⊤

pred : (n : ℕ) → .⦃ NotZero? n ⦄ → ℕ
pred (suc n) = n

nm : ℕ
nm = pred 1

----------------------------------------------------------------------------------------
-- Recursion, termination checker
-- Agda ONLY accepts total functions.

double : ℕ → ℕ
double zero = 0
double (suc n) = suc (suc (double n))

double-test1 : double 2 ≡ 4
double-test1 = refl
double-test2 : double 0 ≡ 0
double-test2 = refl
double-test3 : double 10 ≡ 20
double-test3 = refl

half : ℕ → ℕ
half = {!!}

half-test1 : half 10 ≡ 5
half-test1 = refl
half-test2 : half 11 ≡ 5
half-test2 = refl
half-test3 : half 12 ≡ 6
half-test3 = refl

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)
infixl 6 _+_

+-test1 : 3 + 5 ≡ 8
+-test1 = refl
+-test2 : 0 + 5 ≡ 5
+-test2 = refl
+-test3 : 5 + 0 ≡ 5
+-test3 = refl

_*_ : ℕ → ℕ → ℕ
zero * y = 0
suc x * y = y + x * y
infixl 7 _*_

*-test1 : 3 * 4 ≡ 12
*-test1 = refl
*-test2 : 3 * 1 ≡ 3
*-test2 = refl
*-test3 : 3 * 0 ≡ 0
*-test3 = refl
*-test4 : 0 * 10 ≡ 0
*-test4 = refl

_^_ : ℕ → ℕ → ℕ
x ^ zero = 1
x ^ suc y = x * x ^ y
infixr 8 _^_

^-test1 : 3 ^ 4 ≡ 81
^-test1 = refl
^-test2 : 3 ^ 0 ≡ 1
^-test2 = refl
^-test3 : 0 ^ 3 ≡ 0
^-test3 = refl
^-test4 : 1 ^ 3 ≡ 1
^-test4 = refl
^-test5 : 0 ^ 0 ≡ 1 -- This works over natural numbers, problematic over real numbers.
^-test5 = refl

_! : ℕ → ℕ
zero ! = suc zero
suc x ! = suc x * (x !)

!-test1 : 3 ! ≡ 6
!-test1 = refl
!-test2 : 1 ! ≡ 1
!-test2 = refl
!-test3 : 6 ! ≡ 720
!-test3 = refl

_-_ : ℕ → ℕ → ℕ
x - zero = x
zero - suc y = 0
suc x - suc y = x - y
infixl 6 _-_

-test1 : 3 - 2 ≡ 1
-test1 = refl
-test2 : 3 - 3 ≡ 0
-test2 = refl
-test3 : 3 - 4 ≡ 0 -- ugly thing
-test3 = refl
-- A better version of subtraction can be written.

-- TASK: Determine if the first number is greater than or equal to the second.
_≥_ : ℕ → ℕ → Bool
x ≥ zero = true
zero ≥ suc y = false
suc x ≥ suc y = x ≥ y -- \>= = ≥

≥test1 : 3 ≥ 2 ≡ true
≥test1 = refl
≥test2 : 3 ≥ 3 ≡ true
≥test2 = refl
≥test3 : 3 ≥ 4 ≡ false
≥test3 = refl

-- do not use recursion, use _≥_ instead!
-- TASK: Hopefully self-explanatory.
_>_ : ℕ → ℕ → Bool
x > y = not (y ≥ x)

>test1 : 3 > 2 ≡ true
>test1 = refl
>test2 : 3 > 3 ≡ false
>test2 = refl
>test3 : 3 > 4 ≡ false
>test3 = refl

-- do not use recursion
-- TASK: Hopefully self-explanatory.
_<_ : ℕ → ℕ → Bool
x < y = not (x ≥ y)

<test1 : 3 < 2 ≡ false
<test1 = refl
<test2 : 3 < 3 ≡ false
<test2 = refl
<test3 : 3 < 4 ≡ true
<test3 = refl

-- TASK: Return the smaller of two numbers.
min : ℕ → ℕ → ℕ
min zero y = zero
min (suc x) zero = zero
min (suc x) (suc y) = suc (min x y)

min-test1 : min 3 2 ≡ 2
min-test1 = refl
min-test2 : min 2 3 ≡ 2
min-test2 = refl
min-test3 : min 3 3 ≡ 3
min-test3 = refl

-- TASK: Compare two numbers! If the first is smaller than the second, return the third parameter; if they are equal, return the fourth; if greater, return the fifth.
comp : {A : Set} → ℕ → ℕ → A → A → A → A
comp zero zero m<n m=n m>n = m=n
comp zero (suc n) m<n m=n m>n = m<n
comp (suc m) zero m<n m=n m>n = m>n
comp (suc m) (suc n) m<n m=n m>n = comp m n m<n m=n m>n

comp-test1 : comp {ℕ} 10 10 0 1 2 ≡ 1
comp-test1 = refl
comp-test2 : comp {ℕ} 10 11 0 1 2 ≡ 0
comp-test2 = refl
comp-test3 : comp {ℕ} 12 11 0 1 2 ≡ 2
comp-test3 = refl

-- TASK: Determine the greatest common divisor of two numbers.
-- Hint: Use comp!
gcd : ℕ → ℕ → ℕ
{-# TERMINATING #-} -- Cheating! But this function is not easy to define well enough for Agda to see that it terminates.
gcd m n = comp m n (gcd m (n - m)) m (gcd (m - n) n)

gcd-test1 : gcd 6 9 ≡ 3
gcd-test1 = refl
gcd-test2 : gcd 100 150 ≡ 50
gcd-test2 = refl
gcd-test3 : gcd 17 19 ≡ 1
gcd-test3 = refl
gcd-test4 : gcd 12 24 ≡ 12
gcd-test4 = refl
gcd-test5 : gcd 19 17 ≡ 1
gcd-test5 = refl

-- use the same definition as gcd, but now recursion based on fuel
gcd-helper : ℕ → ℕ → ℕ → ℕ
gcd-helper zero m n = 0
gcd-helper (suc fuel) m n = comp m n (gcd-helper fuel m (n - m)) m (gcd-helper fuel (m - n) n)

gcd' : ℕ → ℕ → ℕ
gcd' m n = gcd-helper (m + n) m n

-- Why does Agda accept this?

gcd'-test1 : gcd' 6 9 ≡ 3
gcd'-test1 = refl
gcd'-test2 : gcd' 100 150 ≡ 50
gcd'-test2 = refl
gcd'-test3 : gcd' 17 19 ≡ 1
gcd'-test3 = refl
gcd'-test4 : gcd' 12 24 ≡ 12
gcd'-test4 = refl
gcd'-test5 : gcd' 19 17 ≡ 1
gcd'-test5 = refl

-- TASK: Is a number even?
even? : ℕ → Bool
even? = {!!}

even?-test1 : even? 3 ≡ false
even?-test1 = refl
even?-test2 : even? 200 ≡ true
even?-test2 = refl

-- TASK: Determine the nth element of the Fibonacci sequence; let the 0th element be 1.
fib : ℕ → ℕ
fib = {!!}

fib-test1 : fib 6 ≡ 13
fib-test1 = refl
fib-test2 : fib 3 ≡ 3
fib-test2 = refl

-- TASK: Determine if two numbers are equal! Do not use recursion!
eq? : ℕ → ℕ → Bool
eq? = {!!}

eq?-test1 : eq? 4 3 ≡ false
eq?-test1 = refl
eq?-test2 : eq? 4 4 ≡ true
eq?-test2 = refl

-- rem m n = the remainder when dividing m by (suc n)
-- TASK: Divide two numbers, the result should be the remainder of the integer division.
rem : ℕ → ℕ → ℕ
rem a b = {!!}
rem-test1 : rem 5 1 ≡ 1
rem-test1 = refl
rem-test2 : rem 11 2 ≡ 2
rem-test2 = refl

-- div m n = the number of times (suc n) is in m
-- TASK: Perform integer division on two numbers!
div : ℕ → ℕ → ℕ
div a b = {!!}
div-test1 : div 5 1 ≡ 2
div-test1 = refl
div-test2 : div 11 2 ≡ 3
div-test2 = refl

-- Why is its name starting with ite?
iteNat : {A : Set} → A → (A → A) → ℕ → A
iteNat z s zero = z
iteNat z s (suc n) = s (iteNat z s n)

recNat : {A : Set} → A → (ℕ → A → A) → ℕ → A
recNat z s zero = z
recNat z s (suc n) = s n (recNat z s n)

-- TASK: define iteNat without pattern matching, using recNat
iteNat' : {A : Set} → A → (A → A) → ℕ → A
iteNat' z s n = recNat z (λ x x₁ → s x₁) n --recNat (λ x x₁ x₂ → {!   !}) (λ x x₁ x₂ x₃ x₄ → {!   !}) {!   !}

iteNat'-test1 : {A : Set}{z : A}{s : A → A} → iteNat' z s zero ≡ z
iteNat'-test1 = refl
iteNat'-test2 : {A : Set}{z : A}{s : A → A}{n : ℕ} → iteNat' z s (suc n) ≡ s (iteNat' z s n)
iteNat'-test2 = refl

itepred : ℕ → ℕ 
itepred n =  snd (iteNat z' s' n )
  where
    z' : ℕ × ℕ
    z' = (0 , 0)
    s' : ℕ × ℕ → ℕ × ℕ
    s' (n , m) = suc n , n
-- TASK: define recNat without pattern matching, using iteNat (see lecture)
recNat' : {A : Set} → A → (ℕ → A → A) → ℕ → A
recNat' {A} z s n = snd (iteNat z' s' n )
  where
    z' : ℕ × A
    z' = (0 , z)
    s' : ℕ × A → ℕ × A
    s' (n , m) = suc n , s n m

recNat'-test1 : {A : Set}{z : A}{s : ℕ → A → A} → recNat' z s zero ≡ z
recNat'-test1 = refl
recNat'-test2 : {A : Set}{z : A}{s : ℕ → A → A} → recNat' z s 3 ≡ s 2 (s 1 (s 0 z))
recNat'-test2 = refl

-- TASK: define all functions above (length, ..., map) again without pattern matching, using iteNat and/or recNat!

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
length = {!!}

length-test1 : length {ℕ} (1 ∷ 2 ∷ 3 ∷ []) ≡ 3
length-test1 = refl
length-test2 : length {ℕ} (1 ∷ []) ≡ 1
length-test2 = refl

-- TASK: Sum the numbers in a list.
sumList : List ℕ → ℕ
sumList = {!!}

sumList-test : sumList (1 ∷ 2 ∷ 3 ∷ []) ≡ 6
sumList-test = refl

-- TASK: Concatenate two lists!
_++_ : {A : Set} → List A → List A → List A
_++_ = {!!}
infixr 5 _++_

++-test : 3 ∷ 2 ∷ [] ++ 1 ∷ 4 ∷ [] ≡ 3 ∷ 2 ∷ 1 ∷ 4 ∷ []
++-test = refl

-- TASK: Apply a function to every element in a list!
map : {A B : Set} → (A → B) → List A → List B
map = {!!}

map-test : map (_+ 2) (3 ∷ 9 ∷ []) ≡ (5 ∷ 11 ∷ [])
map-test = refl

-- TASK: Define the destructor for lists! Process a list:
-- if the list is empty, just return a base value
-- if the list has elements, apply a function to it with the base value right-associated.
-- In Haskell, foldr
iteList : {A B : Set} → B → (A → B → B) → List A → B
iteList n c [] = n
iteList n c (x ∷ as) = c x (iteList n c as)

iteList-testlen : iteList {ℕ} zero (λ x x₁ → suc x₁) (1 ∷ 2 ∷ 4 ∷ []) ≡ 3
iteList-testlen = refl

-- iteList-testmap : iteList {ℕ} [] (λ {zero x₁ → sux₁
--                                    ; (suc x) x₁ → {!   !}}) (1 ∷ 2 ∷ 3 ∷ []) ≡ (2 ∷ 3 ∷ 4 ∷ [])
-- iteList-testmap = refl

iteList-test : iteList {ℕ} [] _∷_ (1 ∷ 2 ∷ 3 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ []
iteList-test = refl

-- iteList-test : iteList 3 _^_ (2 ∷ 3 ∷ []) ≡ 2 ^ (3 ^ 3)
-- iteList-test = refl

-- TASK: define the above functions (length, ..., map) using iteList!

---------------------------------------------------------
-- trees
---------------------------------------------------------

-- a datatype of expressions

data Expr : Set where
  value : ℕ → Expr
  _[+]_ : Expr → Expr → Expr
  _[*]_ : Expr → Expr → Expr

-- Representation of 2 * (3 + 4):
e : Expr
e = value 2 [*] (value 3 [+] value 4)
{-
  *
 / \
2   +
   / \
  3   4
-}

-- TASK: Evaluate an expression!
eval : Expr → ℕ
eval = {!!}

eval-test : eval e ≡ 14
eval-test = refl

-- TASK: Determine the height of an expression tree. The height of a leaf is 0.
height : Expr → ℕ
height = {!!}

height-test : height e ≡ 2
height-test = refl


-- In the http://www.cs.nott.ac.uk/~psztxa/mgs.2021/datatypes.pdf, the 3rd task (page 74):

data Tree (A : Set) : Set where
  leaf : Tree A
  node : Tree A → A → Tree A → Tree A

t : Tree ℕ
t = node (node leaf 1 (node leaf 2 leaf)) 5 leaf
{-
    5
   / \
  1
 / \
    2
   / \
-}

-- TASK: Perform an inorder traversal of a tree!
tree2List : {A : Set} → Tree A → List A
tree2List = {!!}

tree2List-test : tree2List t ≡ 1 ∷ 2 ∷ 5 ∷ []
tree2List-test = refl

-- a tree is ordered if all values in the left subtree are smaller and in the right subtree are larger. for example, t is ordered.
-- hint: use the _≤_ function.
-- this function inserts a new value into an ordered tree so that the tree remains ordered.
insert : ℕ → Tree ℕ → Tree ℕ
insert = {!!}

t' : Tree ℕ
t' = node (node (node leaf 0 leaf) 1 (node leaf 2 leaf)) 5 leaf
{-
      5
     / \
    1
   / \
  0   2
 / \ / \
-}

insert-test : insert 0 t ≡ t'
insert-test = refl

-- TASK: convert a list into an ordered tree.
list2tree : List ℕ → Tree ℕ
list2tree = {!!}

-- TASK: sort a list by converting it to a tree and then performing an inorder traversal!
tree-sort : List ℕ → List ℕ
tree-sort = {!!}

tree-sort-test1 : tree-sort (10 ∷ 2 ∷ 1 ∷ 5 ∷ []) ≡ 1 ∷ 2 ∷ 5 ∷ 10 ∷ []
tree-sort-test1 = refl

tree-sort-test2 : tree-sort (1 ∷ 2 ∷ 1 ∷ 5 ∷ []) ≡ 1 ∷ 1 ∷ 2 ∷ 5 ∷ []
tree-sort-test2 = refl

-- nested types

data RoseTree : Set where
  node : List RoseTree → RoseTree

tR : RoseTree
tR = node (node (node [] ∷ []) ∷ node [] ∷ node (node [] ∷ node [] ∷ []) ∷ [])
{-
  /|\
 |  /\
-}

-- TASK: Count the nodes in a rose tree.
countNodes     : RoseTree → ℕ
countNodesList : List RoseTree → ℕ
countNodes = {!!}
countNodesList = {!!}

countNodes-test : countNodes tR ≡ 7
countNodes-test = refl

-- maximum of two numbers
max : ℕ → ℕ → ℕ
max = {!!}

max-test1 : max 3 2 ≡ 3
max-test1 = refl
max-test2 : max 20 30 ≡ 30
max-test2 = refl
max-test3 : max 20 20 ≡ 20
max-test3 = refl

-- TASK: Determine the height of a rose tree.
heightRoseTree : RoseTree → ℕ
heightRoseTreeList : List RoseTree → ℕ
heightRoseTree = {!!}
heightRoseTreeList = {!!}

heightRoseTree-test1 : heightRoseTree tR ≡ 2
heightRoseTree-test1 = refl
heightRoseTree-test2 : heightRoseTree (node (node (node (node [] ∷ []) ∷ []) ∷ [])) ≡ 3
heightRoseTree-test2 = refl

-- infinitely branching trees

data TreeInf : Set where
  leaf : TreeInf
  node : (ℕ → TreeInf) → TreeInf

-- a balanced tree which has height two (draw it!)
t2 : TreeInf
t2 = node (λ _ → node (λ _ → leaf))

-- tI n should be a complete tree of height n (all branches should have height n-1, and so on)
tI : ℕ → TreeInf
tI = {!!}

tI-test1 : tI 3 ≡ node λ _ → node λ _ → node λ _ → leaf
tI-test1 = refl
tI-test2 : tI 5 ≡ node λ _ → node λ _ → node λ _ → node λ _ → node λ _ → leaf
tI-test2 = refl

-- a tree where the height of the n^th branch is n (all branches have finite length, but there is no upper bound)
tI' : TreeInf
tI' = {!!}

_!_ : TreeInf → ℕ → TreeInf
leaf ! n = leaf
node ts ! n = ts n
test-tI'1 : tI' ! 0 ≡ leaf
test-tI'1 = refl
test-tI'2 : tI' ! 1 ≡ node λ _ → leaf
test-tI'2 = refl
test-tI'3 : tI' ! 3 ≡ node λ _ → node λ _ → node λ _ → leaf
test-tI'3 = refl
test-tI'4 : tI' ! 5 ≡ node λ _ → node λ _ → node λ _ → node λ _ → node λ _ → leaf
test-tI'4 = refl
 