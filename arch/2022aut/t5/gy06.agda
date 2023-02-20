module t5.gy06 where
open import lib hiding (_+_; _*_; _-_; _<_)

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

double : ℕ → ℕ
double zero = zero
double (suc x) = suc (suc (double x))

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)

fib : ℕ → ℕ
fib zero = 1
fib (suc zero) = 1
fib (suc (suc n)) = fib n + fib (suc n)

-- Iterator (iteNat) and recursor (recNat):

iteNat : {A : Type} → A → (A → A) → ℕ → A
iteNat z s zero    = z
iteNat z s (suc n) = s (iteNat z s n)

-- if  n = suc (suc (suc zero))
--   iteNat z s n    =    s (s (s z))

recNat : {A : Type} → A → (ℕ → A → A) → ℕ → A
recNat z s zero    = z
recNat z s (suc n) = s n (recNat z s n)

-- n = suc (suc (suc zero))
-- recNat z s n = s (suc (suc zero)) (s (suc zero) (s zero z))

-- Redefine double, _+_ and fib using recNat or iteNat:

-- double : ℕ → ℕ
-- double zero    = zero
-- double (suc x) = suc (suc (double x))

double' : ℕ → ℕ
double' n = iteNat
            zero
            (λ doublex → suc (suc doublex))
            n

double'-test1 : double' 4 ≡ double 4
double'-test1 = refl
double'-test2 : double' 11 ≡ double 11
double'-test2 = refl

-- half : ℕ → ℕ
-- half zero          = 0
-- half (suc zero)    = 0
-- half (suc (suc n)) = suc (half n)

half'' : ℕ → ℕ × ℕ
half'' zero    = 0 , 0
half'' (suc n) = let hn , hsn = half'' n
                 in hsn , suc hn

-- half'' n ≡ half n , half (suc n)

half = λ n → half'' n .fst

half' : ℕ → ℕ
half' n =
  let result
       = iteNat {ℕ × ℕ}
         (0 , 0)
         -- (λ (halfn , halfsucn) → halfsucn , suc halfn)
         (λ { (x , y) → y , suc x })
         n
  -- result ≡ (half n, half (suc n))
  in result .fst

-- _+_ : ℕ → ℕ → ℕ
-- zero  + b = b
-- suc a + b = suc (a + b)

_+'_ : ℕ → ℕ → ℕ
a +' b = iteNat
         b                              -- zero  + b = b
         -- (λ { aplusb → suc aplusb }) -- suc a + b = suc (a + b)
         suc
         a

+'-test1 : 3 +' 4 ≡ 3 + 4
+'-test1 = refl
+'-test2 : 12 +' 7 ≡ 12 + 7
+'-test2 = refl

-- fib : ℕ → ℕ
-- fib zero = 1
-- fib (suc zero) = 1
-- fib (suc (suc n)) = fib n + fib (suc n)

-- fib'' n ≡ (fib n , fib (suc n))
fib'' : ℕ → ℕ × ℕ
fib'' zero    = 1 , 1
fib'' (suc n) = let fibn , fibsucn = fib'' n
                in fibsucn , fibn + fibsucn -- fib n + fib (suc n)

fib' : ℕ → ℕ
fib' n =
  iteNat -- {ℕ × ℕ}
  (1 , 1)
  (λ { (fibn , fibsucn) → fibsucn , fibn + fibsucn })
  n
  .fst

fib'-test1 : fib' 3 ≡ fib 3
fib'-test1 = refl
fib'-test2 : fib' 8 ≡ fib 8
fib'-test2 = refl

--
-- Accumulator passing definition  ->  iterator
--   iteNat { Acc → Result }
--

plus-acc : ℕ → ℕ → ℕ
plus-acc zero    acc = acc
plus-acc (suc a) acc = plus-acc a (suc acc)

plus-acc' : ℕ → ℕ → ℕ
plus-acc' a acc
  = iteNat {ℕ → ℕ}
    (λ acc → acc)
    (λ f acc → f (suc acc))
    a acc

---------------------------------------------------------
-- lists
---------------------------------------------------------

data List (A : Type) : Type where
  []  : List A
  _∷_ : A → List A → List A   -- \::
infixr 6 _∷_

length : {A : Type} → List A → ℕ
length []       = 0
length (x ∷ xs) = suc (length xs)

length-test1 : length (1 ∷ 2 ∷ 3 ∷ []) ≡ 3
length-test1 = refl
length-test2 : length (1 ∷ []) ≡ 1
length-test2 = refl

sumList : List ℕ → ℕ
sumList [] = 0
sumList (x ∷ xs) = x + sumList xs

-- sumList-test : sumList (1 ∷ 2 ∷ 3 ∷ []) ≡ 6
-- sumList-test = refl

-- _+_ : ℕ → ℕ → ℕ
-- zero  + m = m
-- suc n + m = suc (n + m)

_++_ : {A : Type} → List A → List A → List A
[]     ++ ys = ys
x ∷ xs ++ ys = x ∷ (xs ++ ys)
infixr 5 _++_

-- ++-test : 3 ∷ 2 ∷ [] ++ 1 ∷ 4 ∷ [] ≡ 3 ∷ 2 ∷ 1 ∷ 4 ∷ []
-- ++-test = refl

map : {A B : Type} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

-- map-test : map (_+ 2) (3 ∷ 9 ∷ []) ≡ (5 ∷ 11 ∷ [])
-- map-test = refl

iteList : {A B : Type} → B → (A → B → B) → List A → B
iteList n c [] = n
iteList n c (a ∷ as) = c a (iteList n c as)

-- Redefine some of the above functions (length, ...) using iteList.

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

-- eval-test : eval e ≡ 14
-- eval-test = refl

height : Expr → ℕ
height = {!!}

-- height-test : height e ≡ 2
-- height-test = refl


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
tree2List = {!!}

-- tree2List-test : tree2List t ≡ 1 ∷ 2 ∷ 5 ∷ []
-- tree2List-test = refl

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

-- insert-test : insert 0 t ≡ t'
-- insert-test = refl

-- egy listat egy rendezett fara alakit.
list2tree : List ℕ → Tree ℕ
list2tree = λ _ → leaf

tree-sort : List ℕ → List ℕ
tree-sort = {!!}

-- tree-sort-test1 : tree-sort (10 ∷ 2 ∷ 1 ∷ 5 ∷ []) ≡ 1 ∷ 2 ∷ 5 ∷ 10 ∷ []
-- tree-sort-test1 = refl

-- tree-sort-test2 : tree-sort (1 ∷ 2 ∷ 1 ∷ 5 ∷ []) ≡ 1 ∷ 1 ∷ 2 ∷ 5 ∷ []
-- tree-sort-test2 = refl

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
countNodes = {!!}
countNodesList = {!!}

-- countNodes-test : countNodes tR ≡ 7
-- countNodes-test = refl

-- maximum of two numbers
max : ℕ → ℕ → ℕ
max = {!!}

-- max-test1 : max 3 2 ≡ 3
-- max-test1 = refl
-- max-test2 : max 20 30 ≡ 30
-- max-test2 = refl
-- max-test3 : max 20 20 ≡ 20
-- max-test3 = refl

heightRoseTree : RoseTree → ℕ
heightRoseTreeList : List RoseTree → ℕ
heightRoseTree = {!!}
heightRoseTreeList = {!!}

-- heightRoseTree-test1 : heightRoseTree tR ≡ 2
-- heightRoseTree-test1 = refl
-- heightRoseTree-test2 : heightRoseTree (node (node (node (node [] ∷ []) ∷ []) ∷ [])) ≡ 3
-- heightRoseTree-test2 = refl

-- vegtelenul elagazodo fak (infinitely branching trees)

data TreeInf : Type where
  leaf : TreeInf
  node : (ℕ → TreeInf) → TreeInf

-- a balanced tree which has height two (draw it!)
t2 : TreeInf
t2 = node (λ _ → node (λ _ → leaf))

-- tI n should be a complete tree of height n (all branches should have height n-1, and so on)
tI : ℕ → TreeInf
tI = {!!}

-- tI-test1 : tI 3 ≡ node λ _ → node λ _ → node λ _ → leaf
-- tI-test1 = refl
-- tI-test2 : tI 5 ≡ node λ _ → node λ _ → node λ _ → node λ _ → node λ _ → leaf
-- tI-test2 = refl

-- a tree where the height of the n^th branch is n (all branches have finite length, but there is no upper bound)
tI' : TreeInf
tI' = {!!}

_!_ : TreeInf → ℕ → TreeInf
leaf ! n = leaf
node ts ! n = ts n

-- test-tI'1 : tI' ! 0 ≡ leaf
-- test-tI'1 = refl
-- test-tI'2 : tI' ! 1 ≡ node λ _ → leaf
-- test-tI'2 = refl
-- test-tI'3 : tI' ! 3 ≡ node λ _ → node λ _ → node λ _ → leaf
-- test-tI'3 = refl
-- test-tI'4 : tI' ! 5 ≡ node λ _ → node λ _ → node λ _ → node λ _ → node λ _ → leaf
-- test-tI'4 = refl
