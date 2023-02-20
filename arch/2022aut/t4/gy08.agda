module t4.gy08 where
open import lib

-- List of unicode symbols:
--    →       \to
--            \rightarrow
--    ℕ       \bN           'b'lackboard 'N', there is also \bZ for ℤ, etc
--    λ       \Gl           'G'reek 'l', there is also \GG for Γ, etc
--            \lambda
--    ×       \times
--    ⊎       \u+
--    ⊤       \top
--    ⊥       \bot
--    ↔       \lr
--    ₁       \_1
--    ₐ       \_a
--    ¹       \^1

---------------------------------------------------------
-- lists
---------------------------------------------------------

data List (A : Type) : Type where
  []  : List A
  _∷_ : A → List A → List A
infixr 6 _∷_

-- List ⊤ ≅ ℕ

length : {A : Type} → List A → ℕ
length []       = 0
length (x ∷ xs) = 1 + length xs -- we can only use  length xs
      --  ^  \::

length-test1 : length (1 ∷ 2 ∷ 3 ∷ []) ≡ 3
length-test1 = refl
length-test2 : length (1 ∷ []) ≡ 1
length-test2 = refl

sumList : List ℕ → ℕ
sumList []       = 0
sumList (x ∷ xs) = x + sumList xs

sumList-test : sumList (1 ∷ 2 ∷ 3 ∷ []) ≡ 6
sumList-test = refl

-- cons = ∷
-- snoc : List A → A → List A

_++_ : {A : Type} → List A → List A → List A
-- xs ++ [] = xs
-- xs ++ x ∷ ys = {!(snoc xs x) ++ ys!}
[]     ++ ys = ys
x ∷ xs ++ ys = x ∷ (xs ++ ys)
infixr 5 _++_

_+'_ : ℕ → ℕ → ℕ

-- []     ++ ys = ys
zero  +' m = m

-- x ∷ xs ++ ys = x ∷ (xs ++ ys)
suc n +' m = suc (n +' m)

++-test : 3 ∷ 2 ∷ [] ++ 1 ∷ 4 ∷ [] ≡ 3 ∷ 2 ∷ 1 ∷ 4 ∷ []
++-test = refl

map : {A B : Type} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

map-test : map (_+ 2) (3 ∷ 9 ∷ []) ≡ (5 ∷ 11 ∷ [])
map-test = refl

iteList : {A B : Type} → B → (A → B → B) → List A → B
iteList n c [] = n
iteList n c (a ∷ as) = c a (iteList n c as)

-- Redefine some of the above functions (length, ...) using iteList.

length' : {A : Type} → List A → ℕ
length' xs = iteList 0 (λ _ l → l + 1) xs

_++'_ : {A : Type} → List A → List A → List A
xs ++' ys = iteList ys _∷_ xs

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
eval (const n)   = n
eval (el [+] er) = eval el + eval er
eval (el [*] er) = eval el * eval er

eval-test : eval e ≡ 14
eval-test = refl

-- maximum of two numbers
max : ℕ → ℕ → ℕ
max zero zero = zero
max zero (suc m) = suc m
max (suc n) zero = suc n
max (suc n) (suc m) = suc (max n m)

max-test1 : max 3 2 ≡ 3
max-test1 = refl
max-test2 : max 20 30 ≡ 30
max-test2 = refl
max-test3 : max 20 20 ≡ 20
max-test3 = refl

height : Expr → ℕ
height (const x)   = 0
height (el [+] er) = 1 + max (height el) (height er)
height (el [*] er) = 1 + max (height el) (height er)

height-test : height e ≡ 2
height-test = refl

-- http://www.cs.nott.ac.uk/~psztxa/mgs.2021/datatypes.pdf -ben a 3. feladat (74. oldal):

data Tree (A : Type) : Type where
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


tree2List : {A : Type} → Tree A → List A
tree2List leaf = []
tree2List (node tl x tr) = tree2List tl ++ (x ∷ tree2List tr)

tree2List-test : tree2List t ≡ 1 ∷ 2 ∷ 5 ∷ []
tree2List-test = refl

_≤?_ : ℕ → ℕ → Bool
zero ≤? m = true
suc n ≤? zero = false
suc n ≤? suc m = n ≤? m

-- egy fa rendezett, ha minden csomopontnal levo erteknel a bal reszfaban kisebb, a kobb reszfaban pedig nagyobb ertekek vannak. peldaul t rendezett

-- ez a fuggveny egy rendezett faba illeszt be egy uj erteket ugy,
-- hogy a fa rendezett maradjon
insert : ℕ → Tree ℕ → Tree ℕ
insert x leaf = node leaf x leaf
insert x (node tl y tr)
  = if x ≤? y
    then node (insert x tl) y tr
    else node tl y (insert x tr)

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
list2tree []       = leaf
list2tree (x ∷ xs) = insert x (list2tree xs)

tree-sort : List ℕ → List ℕ
tree-sort xs = tree2List (list2tree xs)

tree-sort-test1 : tree-sort (10 ∷ 2 ∷ 1 ∷ 5 ∷ []) ≡ 1 ∷ 2 ∷ 5 ∷ 10 ∷ []
tree-sort-test1 = refl

tree-sort-test2 : tree-sort (1 ∷ 2 ∷ 1 ∷ 5 ∷ []) ≡ 1 ∷ 1 ∷ 2 ∷ 5 ∷ []
tree-sort-test2 = refl

-- nested types

data RoseTree : Type where
  node : List RoseTree → RoseTree

tR : RoseTree
tR = node (node (node [] ∷ []) ∷ node [] ∷ node (node [] ∷ node [] ∷ []) ∷ [])
{-
  /|\
 |  /\
-}

countNodes     : RoseTree → ℕ
countNodesList : List RoseTree → ℕ
countNodes (node xs) = 1 + countNodesList xs
countNodesList [] = 0
countNodesList (x ∷ xs) = countNodes x + countNodesList xs

countNodes-test : countNodes tR ≡ 7
countNodes-test = refl

heightRoseTree : RoseTree → ℕ
heightRoseTreeList : List RoseTree → ℕ
heightRoseTree (node xs) = heightRoseTreeList xs
heightRoseTreeList [] = 0
heightRoseTreeList (x ∷ xs) = max (1 + heightRoseTree x) (heightRoseTreeList xs)

heightRoseTree-test1 : heightRoseTree tR ≡ 2
heightRoseTree-test1 = refl
heightRoseTree-test2 : heightRoseTree (node (node (node (node [] ∷ []) ∷ []) ∷ [])) ≡ 3
heightRoseTree-test2 = refl

-- vegtelenul elagazodo fak (infinitely branching trees)

data TreeInf : Type where
  leaf : TreeInf
  node : (ℕ → TreeInf) → TreeInf

-- a balanced tree which has height two (draw it!)
t2 : TreeInf
t2 = node (λ _ → node (λ _ → leaf))

-- tI n should be a complete tree of height n (all branches should have height n-1, and so on)
tI : ℕ → TreeInf
tI zero = leaf
tI (suc n) = node (λ _ → tI n)

tI-test1 : tI 3 ≡ node λ _ → node λ _ → node λ _ → leaf
tI-test1 = refl
tI-test2 : tI 5 ≡ node λ _ → node λ _ → node λ _ → node λ _ → node λ _ → leaf
tI-test2 = refl

-- a tree where the height of the n^th branch is n (all branches have finite length, but there is no upper bound)
tI' : TreeInf
tI' = node tI

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
