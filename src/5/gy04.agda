{-# OPTIONS --guardedness #-}
open import lib

------------------------------------------
-- kvizmegoldás
------------------------------------------

add-if : ℕ → ℕ
add-if zero = 2
add-if (suc zero) = 4
add-if (suc (suc x)) = suc (suc (add-if x))

test-1 : add-if 3 ≡ 6
test-1 = refl
test-2 : add-if 6 ≡ 8
test-2 = refl
test-3 : add-if 15 ≡ 18
test-3 = refl
test-4 : add-if 2 ≡ 4
test-4 = refl

---------------------------------------------

data Maybe A : Set where
  Nothing : Maybe A
  Just    : A → Maybe A

_≥_ : ℕ → ℕ → Bool
_≥_ _ zero = true
_≥_ zero _ = false
_≥_ (suc n) (suc m) = n ≥ m

≥test1 : 3 ≥ 2 ≡ true
≥test1 = refl
≥test2 : 3 ≥ 3 ≡ true
≥test2 = refl
≥test3 : 3 ≥ 4 ≡ false
≥test3 = refl

-- ne hasznalj rekurziot, hanem hasznald _≥_-t!
_>_ : ℕ → ℕ → Bool
_>_ m n = (m - n) ≥ 1

>test1 : 3 > 2 ≡ true
>test1 = refl
>test2 : 3 > 3 ≡ false
>test2 = refl
>test3 : 3 > 4 ≡ false
>test3 = refl

comp : {A : Set} → ℕ → ℕ → A → A → A → A
comp m n m<n m=n m>n = if m < n then m<n else (if m > n then m>n else m=n)

comp-test1 : comp 10 10 0 1 2 ≡ 1
comp-test1 = refl
comp-test2 : comp 10 11 0 1 2 ≡ 0
comp-test2 = refl
comp-test3 : comp 12 11 0 1 2 ≡ 2
comp-test3 = refl

---------------------------------------------------------
-- lists
---------------------------------------------------------

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A
infixr 6 _∷_

length : {A : Set} → List A → ℕ
length [] = 0
length (x ∷ x₁) = 1 + length x₁

length-test1 : length (1 ∷ 2 ∷ 3 ∷ []) ≡ 3
length-test1 = refl
length-test2 : length (1 ∷ []) ≡ 1
length-test2 = refl

sumList : List ℕ → ℕ
sumList [] = 0
sumList (x ∷ x₁) = x + sumList x₁

sumList-test : sumList (1 ∷ 2 ∷ 3 ∷ []) ≡ 6
sumList-test = refl

_++_ : {A : Set} → List A → List A → List A
[] ++ x₁ = x₁
x ∷ x₂ ++ x₁ = x ∷ (x₂ ++ x₁)
infixr 5 _++_

++-test : 3 ∷ 2 ∷ [] ++ 1 ∷ 4 ∷ [] ≡ 3 ∷ 2 ∷ 1 ∷ 4 ∷ []
++-test = refl

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

map-test : map (_+ 2) (3 ∷ 9 ∷ []) ≡ (5 ∷ 11 ∷ [])
map-test = refl

iteList : {A B : Set} → B → (A → B → B) → List A → B
iteList n c [] = n
iteList n c (a ∷ as) = c a (iteList n c as)

-- FEL: add meg a fenti fuggvenyeket (length, ..., map) iteList segitsegevel!

length' : {A : Set} → List A → ℕ
length' = iteList 0 (λ _ x₂ → suc x₂)

length-test-1 : length' (1 ∷ 2 ∷ 3 ∷ []) ≡ 3
length-test-1 = refl
length-test-2 : length' (1 ∷ []) ≡ 1
length-test-2 = refl

sum : List ℕ → ℕ
sum x = iteList 0 (λ x₁ x₂ → x₁ + x₂) x

map' : {A B : Set} → (A → B) → List A → List B
map' f = iteList [] (λ a neut → f a ∷ neut)

-- FEL: add meg recNat-ot, es vezesd vissza iteNat-ra!

---------------------------------------------------------
-- trees
---------------------------------------------------------

-- a datatype of expressions

data Expr : Set where
  const : ℕ → Expr
  _[+]_ : Expr → Expr → Expr
  _[*]_ : Expr → Expr → Expr

-- 2 * (3 + 4) reprezentacioja:
e : Expr
e = const 2 [*] (const 3 [+] const 4)
{-
  *
 / \
2   +
   / \
  3   4
-}

eval : Expr → ℕ
eval = {!!}

eval-test : eval e ≡ 14
eval-test = refl

height : Expr → ℕ
height = {!!}

height-test : height e ≡ 2
height-test = refl


-- http://www.cs.nott.ac.uk/~psztxa/mgs.2021/datatypes.pdf -ben a 3. feladat (74. oldal):

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


tree2List : {A : Set} → Tree A → List A
tree2List leaf = []
tree2List (node x x₁ x₂) = tree2List x ++ (x₁ ∷ tree2List x₂)

tree2List-test : tree2List t ≡ 1 ∷ 2 ∷ 5 ∷ []
tree2List-test = refl

preorder : {A : Set} → Tree A → List A
preorder leaf = []
preorder (node x x₁ x₂) = x₁ ∷ preorder x ++ preorder x₂

postorder : {A : Set} → Tree A → List A
postorder leaf = []
postorder (node x x₁ x₂) = postorder x ++ postorder x₂ ++ x₁ ∷ []

_≤?_ : ℕ → ℕ → Bool
zero ≤? m = true
suc n ≤? zero = false
suc n ≤? suc m = n ≤? m

-- egy fa rendezett, ha minden csomopontnal levo erteknel a bal reszfaban kisebb, a kobb reszfaban pedig nagyobb ertekek vannak. peldaul t rendezett

-- ez a fuggveny egy rendezett faba illeszt be egy uj erteket ugy,
-- hogy a fa rendezett maradjon
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

-- egy listat egy rendezett fara alakit.
list2tree : List ℕ → Tree ℕ
list2tree = {!   !}

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

{-# TERMINATING #-}
countNodes     : RoseTree → ℕ
countNodes (node x) = suc (iteList 0 (λ rt neut → countNodes rt + neut) x)

countNodesList : List RoseTree → ℕ
countNodesList [] = 0
countNodesList (x ∷ x₁) = countNodes x + countNodesList x₁

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

heightRoseTree : RoseTree → ℕ
heightRoseTreeList : List RoseTree → ℕ
heightRoseTree = {!!}
heightRoseTreeList = {!!}

heightRoseTree-test1 : heightRoseTree tR ≡ 2
heightRoseTree-test1 = refl
heightRoseTree-test2 : heightRoseTree (node (node (node (node [] ∷ []) ∷ []) ∷ [])) ≡ 3
heightRoseTree-test2 = refl

-- vegtelenul elagazodo fak (infinitely branching trees)

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


---------------------------------------------------------
-- positivity
---------------------------------------------------------

{-# NO_POSITIVITY_CHECK #-}
data Tm : Set where
  lam : (Tm → Tm) → Tm

{-
data Tm = Lam (Tm -> Tm)
-}

app : Tm → (Tm → Tm)
app (lam x) = x

self-apply : Tm
self-apply = lam (λ t → app t t)

-- C-c C-n this:
Ω : Tm
Ω = app self-apply self-apply

{-# NO_POSITIVITY_CHECK #-}
data Weird : Set where
  foo : (Weird → ⊥) → Weird

{-
data Weird = Foo (Weird -> ⊥)
-}

unweird : Weird → ⊥
unweird (foo x) = x (foo x)

bad : ⊥
bad = unweird (foo unweird)

---------------------------------------------------------
-- coinductive types
---------------------------------------------------------

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream

-- check that the type of head : Stream A → A
--                        tail : Stream A → Stream A

zeroes : Stream ℕ
head zeroes = 0
tail zeroes = zeroes

-- by pattern match on n
countDownFrom : ℕ → List ℕ
countDownFrom n = {!!}

-- from n is not by pattern match on n
from : ℕ → Stream ℕ
head (from n) = n
tail (from n) = from (1 + n)

-- pointwise addition
zipWith : {A B C : Set} → (A → B → C) → Stream A → Stream B → Stream C
zipWith = {!!}

filterL : {A : Set} → (A → Bool) → List A → List A
filterL = {!!}

-- this cannot be defined:
-- filterS : {A : Set} → (A → Bool) → Stream A → Stream A
-- filterS P xs = ?

-- one element from the first stream, then from the second stream, then from the first, and so on
interleave : {A : Set} → Stream A → Stream A → Stream A
interleave = {!!}

-- get the n^th element of the stream
get : {A : Set} → ℕ → Stream A → A
get = {!!}

-- byIndices [0,2,3,2,...] [1,2,3,4,5,...] = [1,3,4,2,...]
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
