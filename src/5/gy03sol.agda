open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_+_; _*_; _-_; _<_)
open import Lib.Containers.List hiding (length; _++_; map; iteList)
open import Lib.Equality
open import Lib.Bool
open import Lib.Empty


---------------------------------------------------------
-- natural numbers
---------------------------------------------------------

{-
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
-}

-- mintát így lehet illeszteni rá:
isZero : ℕ -> Bool
isZero zero = true
isZero (suc n) = false

data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A

-- 0-ra adjon nothingot;
-- többire meg justba csomagolva az előzőjét
pred : ℕ → Maybe ℕ
pred zero = nothing
pred (suc n) = just n

-- a pred inverze
zerosuc : Maybe ℕ → ℕ
zerosuc (just n) = suc n
zerosuc nothing = zero

-- tesztek
pred↔zerosuc-test1 : pred (zerosuc nothing) ≡ nothing
pred↔zerosuc-test1 = refl
pred↔zerosuc-test2 : {n : ℕ} → pred (zerosuc (just n)) ≡ just n
pred↔zerosuc-test2 = refl

-- adja vissza a paraméter kétszeresét
double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))     -- 2 * (1 + n) = 2 + 2 * n = suc (suc (double n))

double-test1 : double 2 ≡ 4
double-test1 = refl
double-test2 : double 0 ≡ 0
double-test2 = refl
double-test3 : double 10 ≡ 20
double-test3 = refl

-- ez izgalmasabb:
-- adja vissza a paraméter felét; lefelé kerekítve
half : ℕ → ℕ
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

half-test1 : half 10 ≡ 5
half-test1 = refl
half-test2 : half 11 ≡ 5
half-test2 = refl
half-test3 : half 12 ≡ 6
half-test3 = refl

_+_ : ℕ → ℕ → ℕ
zero + m = m
-- n + zero = n   -- hatékonyságot javítja
suc n + m = suc (n + m)
infixl 6 _+_

{-
2 + 3 =
= suc (suc zero) + suc (suc (suc zero))
= suc (suc zero + suc (suc (suc zero)))
= suc (suc (zero + suc (suc (suc zero))))
= suc (suc (suc (suc (suc zero))))
= 5
-}

+-test1 : 3 + 5 ≡ 8
+-test1 = refl
+-test2 : 0 + 5 ≡ 5
+-test2 = refl
+-test3 : 5 + 0 ≡ 5
+-test3 = refl

_*_ : ℕ → ℕ → ℕ
zero * m = zero
suc n * m = m + n * m     -- (1 + n) * m = 1 * m + n * m = m + n * m
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
n ^ zero = 1
n ^ suc m = n * n ^ m    -- n ^ (1 + m) = n * n ^ m
infixr 8 _^_

^-test1 : 3 ^ 4 ≡ 81
^-test1 = refl
^-test2 : 3 ^ 0 ≡ 1
^-test2 = refl
^-test3 : 0 ^ 3 ≡ 0
^-test3 = refl
^-test4 : 1 ^ 3 ≡ 1
^-test4 = refl
^-test5 : 0 ^ 0 ≡ 1 -- csúnya dolog
^-test5 = refl

_! : ℕ → ℕ
_! = {!!}

!-test1 : 3 ! ≡ 6
!-test1 = refl
!-test2 : 1 ! ≡ 1
!-test2 = refl
!-test3 : 6 ! ≡ 720
!-test3 = refl

_-_ : ℕ → ℕ → ℕ
zero - m = zero
suc n - zero = suc n
suc n - suc m = n - m
infixl 6 _-_

-test1 : 3 - 2 ≡ 1
-test1 = refl
-test2 : 3 - 3 ≡ 0
-test2 = refl
-test3 : 3 - 4 ≡ 0 -- csúnya dolog
-test3 = refl

_≥_ : ℕ → ℕ → Bool
n ≥ zero = true
zero ≥ suc m = false
suc n ≥ suc m = n ≥ m      -- \ge

≥test1 : 3 ≥ 2 ≡ true
≥test1 = refl
≥test2 : 3 ≥ 3 ≡ true
≥test2 = refl
≥test3 : 3 ≥ 4 ≡ false
≥test3 = refl

-- ne hasznalj rekurziot, hanem hasznald _≥_-t!
_>_ : ℕ → ℕ → Bool
n > m = n ≥ (suc m)

>test1 : 3 > 2 ≡ true
>test1 = refl
>test2 : 3 > 3 ≡ false
>test2 = refl
>test3 : 3 > 4 ≡ false
>test3 = refl

_<_ : ℕ → ℕ → Bool
n < m = m > n
<test1 : 3 < 2 ≡ false
<test1 = refl
<test2 : 3 < 3 ≡ false
<test2 = refl
<test3 : 3 < 4 ≡ true
<test3 = refl

min : ℕ → ℕ → ℕ
min zero m = zero
min (suc n) zero = zero
min (suc n) (suc m) = suc (min n m)

min-test1 : min 3 2 ≡ 2
min-test1 = refl
min-test2 : min 2 3 ≡ 2
min-test2 = refl
min-test3 : min 3 3 ≡ 3
min-test3 = refl

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

-- hasznald comp-ot!
{-
10 8
2   8
2   6
2   4
2   2
-}
gcd : ℕ → ℕ → ℕ
{-# TERMINATING #-}
gcd zero zero = 42 -- itt valójában nincs értelme
gcd zero m     = m
gcd m     zero = m
gcd m n = comp m n
                    (gcd m (n - m))    -- m<n
                    m                        -- m
                    (gcd (m - n) n)     -- m>n

b : ⊥
{-# TERMINATING #-}
b = b

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

-- hasznald ugyanazt a definiciot, mint gcd-nel, de most fuel szerinti rekurzio
gcd-helper : ℕ → ℕ → ℕ → ℕ
-- gcd-helper _ zero zero = ?
-- zero-kat le kéne kezelni
gcd-helper zero m n = 42
gcd-helper (suc fuel) m n = comp m n
                                              (gcd-helper fuel m (n - m))
                                              m
                                              (gcd-helper fuel (m - n) n)
gcd' : ℕ → ℕ → ℕ
gcd' m n = gcd-helper (m + n) m n

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

even? : ℕ → Bool
even? = {!!}

even?-test1 : even? 3 ≡ false
even?-test1 = refl
even?-test2 : even? 200 ≡ true
even?-test2 = refl

fib : ℕ → ℕ
fib = {!!}

{-
1 2 3 4 5 6 7
1 1 2 3 5 8 13
-}

fib-test1 : fib 7 ≡ 13
fib-test1 = refl
fib-test2 : fib 4 ≡ 3
fib-test2 = refl

eq? : ℕ → ℕ → Bool
eq? = {!!}

eq?-test1 : eq? 4 3 ≡ false
eq?-test1 = refl
eq?-test2 : eq? 4 4 ≡ true
eq?-test2 = refl

-- rem m n = a maradek, ha elosztjuk m-et (suc n)-el
rem : ℕ → ℕ → ℕ
rem a zero = 444444444   -- ezt majd egyszer elegánsabban megoldjuk
-- rem a b = if b ≥ a then a else {!rem (a - b) b!}
rem a b = rem-helper (suc a) a b
  where
  rem-helper : ℕ -> ℕ -> ℕ -> ℕ
  rem-helper 0 a b = 42
  rem-helper (suc fuel) a b = if a ≥ b then rem-helper fuel (a - b) b else a

rem-test1 : rem 5 1 ≡ 0
rem-test1 = refl
rem-test2 : rem 11 2 ≡ 1
rem-test2 = refl

-- div m n = m-ben hanyszor van meg (suc n)
div : ℕ → ℕ → ℕ
div a b = {!!}
div-test1 : div 5 1 ≡ 2
div-test1 = refl
div-test2 : div 11 2 ≡ 3
div-test2 = refl

iteNat : {A : Set} → A → (A → A) → ℕ → A
iteNat z s zero = z
iteNat z s (suc n) = s (iteNat z s n)

recNat : {A : Set} → A → (ℕ → A → A) → ℕ → A
recNat z s zero = z
recNat z s (suc n) = s n (recNat z s n)

-- FEL: add meg iteNat-ot mintaillesztes nelkul, recNat segitsegevel
iteNat' : {A : Set} → A → (A → A) → ℕ → A
iteNat' = {!!}

iteNat'-test1 : {A : Set}{z : A}{s : A → A} → iteNat' z s zero ≡ z
iteNat'-test1 = refl
iteNat'-test2 : {A : Set}{z : A}{s : A → A}{n : ℕ} → iteNat' z s (suc n) ≡ s (iteNat' z s n)
iteNat'-test2 = refl

-- FEL: add meg recNat-ot mintaillesztes nelkul, iteNat segitsegevel (lasd eloadas)
recNat' : {A : Set} → A → (ℕ → A → A) → ℕ → A
recNat' = {!!}

recNat'-test1 : {A : Set}{z : A}{s : ℕ → A → A} → recNat' z s zero ≡ z
recNat'-test1 = refl
recNat'-test2 : {A : Set}{z : A}{s : ℕ → A → A} → recNat' z s 3 ≡ s 2 (s 1 (s 0 z))
recNat'-test2 = refl

-- FEL: add meg ujra az osszes fent fuggvenyt mintaillesztes nelkul, iteNat es/vagy recNat hasznalataval!

---------------------------------------------------------
-- lists
---------------------------------------------------------

{-
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A            \:: (backslash kettőspont kettőspont)
infixr 5 _∷_
-}

length : {A : Set} → List A → ℕ
length [] = {!!}
length (x ∷ xs) = {!!}

length-test1 : length {ℕ} (1 ∷ 2 ∷ 3 ∷ []) ≡ 3
length-test1 = refl
length-test2 : length {ℕ} (1 ∷ []) ≡ 1
length-test2 = refl

sumList : List ℕ → ℕ
sumList = {!!}

sumList-test : sumList (1 ∷ 2 ∷ 3 ∷ []) ≡ 6
sumList-test = refl

_++_ : {A : Set} → List A → List A → List A
_++_ = {!!}
infixr 5 _++_

++-test : 3 ∷ 2 ∷ [] ++ 1 ∷ 4 ∷ [] ≡ 3 ∷ 2 ∷ 1 ∷ 4 ∷ []
++-test = refl

map : {A B : Set} → (A → B) → List A → List B
map = {!!}

map-test : map (_+ 2) (3 ∷ 9 ∷ []) ≡ (5 ∷ 11 ∷ [])
map-test = refl

-- foldr
iteList : {A B : Set} → B → (A → B → B) → List A → B
iteList n c [] = n
iteList n c (a ∷ as) = c a (iteList n c as)

-- FEL: add meg a fenti fuggvenyeket (length, ..., map) iteList segitsegevel!

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
eval (const x) = x
eval (t [+] t₁) = eval t + eval t₁
eval (t [*] t₁) = eval t * eval t₁

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
tree2List (node t₁ x t₂) = tree2List t₁ ++ x ∷ tree2List t₂

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
list2tree = λ _ → leaf

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
