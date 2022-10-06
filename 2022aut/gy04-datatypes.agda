open import lib hiding (_+_; _*_; _-_; _<_)

---------------------------------------------------------
-- natural numbers
---------------------------------------------------------

data Maybe A : Type where
  Nothing : Maybe A
  Just    : A → Maybe A

pred : ℕ → Maybe ℕ
pred zero = Nothing
pred (suc n) = Just n

zerosuc : Maybe ℕ → ℕ
zerosuc = {!!}

pred↔zerosuc-test1 : pred (zerosuc Nothing) ≡ Nothing
pred↔zerosuc-test1 = refl
pred↔zerosuc-test2 : {n : ℕ} → pred (zerosuc (Just n)) ≡ Just n
pred↔zerosuc-test2 = refl

double : ℕ → ℕ
double = {!!}

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
_+_ = {!!}
infixl 6 _+_

+-test1 : 3 + 5 ≡ 8
+-test1 = refl
+-test2 : 0 + 5 ≡ 5
+-test2 = refl
+-test3 : 5 + 0 ≡ 5
+-test3 = refl

_*_ : ℕ → ℕ → ℕ
_*_ = {!!}
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
_^_ = {!!}
infixl 8 _^_

^-test1 : 3 ^ 4 ≡ 81
^-test1 = refl
^-test2 : 3 ^ 0 ≡ 1
^-test2 = refl
^-test3 : 0 ^ 3 ≡ 0
^-test3 = refl
^-test4 : 1 ^ 3 ≡ 1
^-test4 = refl
^-test5 : 0 ^ 0 ≡ 1
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
_-_ = {!!}
infixl 6 _-_

-test1 : 3 - 2 ≡ 1
-test1 = refl
-test2 : 3 - 3 ≡ 0
-test2 = refl
-test3 : 3 - 4 ≡ 0
-test3 = refl

_≥_ : ℕ → ℕ → Bool
_≥_ = {!!}

≥test1 : 3 ≥ 2 ≡ true
≥test1 = refl
≥test2 : 3 ≥ 3 ≡ true
≥test2 = refl
≥test3 : 3 ≥ 4 ≡ false
≥test3 = refl

-- ne hasznalj rekurziot, hanem hasznald _≥_-t!
_>_ : ℕ → ℕ → Bool
_>_ = {!!}

>test1 : 3 > 2 ≡ true
>test1 = refl
>test2 : 3 > 3 ≡ false
>test2 = refl
>test3 : 3 > 4 ≡ false
>test3 = refl

_<_ : ℕ → ℕ → Bool
_<_ = {!!}

<test1 : 3 < 2 ≡ false
<test1 = refl
<test2 : 3 < 3 ≡ false
<test2 = refl
<test3 : 3 < 4 ≡ true
<test3 = refl

min : ℕ → ℕ → ℕ
min = {!!}

min-test1 : min 3 2 ≡ 2
min-test1 = refl
min-test2 : min 2 3 ≡ 2
min-test2 = refl
min-test3 : min 3 3 ≡ 3
min-test3 = refl

comp : {A : Type} → ℕ → ℕ → A → A → A → A
comp m n m<n m=n m>n = {!!}

comp-test1 : comp 10 10 0 1 2 ≡ 1
comp-test1 = refl
comp-test2 : comp 10 11 0 1 2 ≡ 0
comp-test2 = refl
comp-test3 : comp 12 11 0 1 2 ≡ 2
comp-test3 = refl

-- hasznald comp-ot!
gcd : ℕ → ℕ → ℕ
{-# TERMINATING #-}
gcd m n = {!!}

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
gcd-helper zero m n = 42
gcd-helper (suc fuel) m n = {!!}
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

not : Bool → Bool
not true = false
not false = true

even? : ℕ → Bool
even? = {!!}

even?-test1 : even? 3 ≡ true
even?-test1 = refl
even?-test2 : even? 200 ≡ false
even?-test2 = refl

fib : ℕ → ℕ
fib = {!!}

fib-test1 : fib 6 ≡ 13
fib-test1 = refl
fib-test2 : fib 3 ≡ 3
fib-test2 = refl

-- rem m n = a maradek, ha elosztjuk m-et (suc n)-el
rem : ℕ → ℕ → ℕ
rem a b = {!!}
rem-test1 : rem 5 1 ≡ 1
rem-test1 = refl
rem-test2 : rem 11 2 ≡ 2
rem-test2 = refl

-- div m n = m-ben hanyszor van meg (suc n)
div : ℕ → ℕ → ℕ
div a b = {!!}
div-test1 : div 5 1 ≡ 2
div-test1 = refl
div-test2 : div 11 2 ≡ 3
div-test2 = refl

iteNat : {A : Type} → A → (A → A) → ℕ → A
iteNat z s zero = z
iteNat z s (suc n) = s (iteNat z s n)

recNat : {A : Type} → A → (ℕ → A → A) → ℕ → A
recNat z s zero = z
recNat z s (suc n) = s n (recNat z s n)

-- FEL: add meg iteNat-ot mintaillesztes nelkul, recNat segitsegevel
iteNat' : {A : Type} → A → (A → A) → ℕ → A
iteNat' = {!!}

iteNat'-test1 : {A : Type}{z : A}{s : A → A} → iteNat' z s zero ≡ z
iteNat'-test1 = refl
iteNat'-test2 : {A : Type}{z : A}{s : A → A}{n : ℕ} → iteNat' z s (suc n) ≡ s (iteNat' z s n)
iteNat'-test2 = refl

-- FEL: add meg recNat-ot mintaillesztes nelkul, iteNat segitsegevel (lasd eloadas)
recNat' : {A : Type} → A → (ℕ → A → A) → ℕ → A
recNat' = {!!}

recNat'-test1 : {A : Type}{z : A}{s : ℕ → A → A} → recNat' z s zero ≡ z
recNat'-test1 = refl
recNat'-test2 : {A : Type}{z : A}{s : ℕ → A → A} → recNat' z s 3 ≡ s 2 (s 1 (s 0 z))
recNat'-test2 = refl

-- FEL: add meg ujra az osszes fent fuggvenyt mintaillesztes nelkul, iteNat es/vagy recNat hasznalataval!

---------------------------------------------------------
-- lists
---------------------------------------------------------

data List (A : Type) : Type where
  [] : List A
  _∷_ : A → List A → List A
infixr 6 _∷_

length : {A : Type} → List A → ℕ
length = {!!}

length-test1 : length (1 ∷ 2 ∷ 3 ∷ []) ≡ 3
length-test1 = refl
length-test2 : length (1 ∷ []) ≡ 1
length-test2 = refl

sumList : List ℕ → ℕ
sumList = {!!}

sumList-test : sumList (1 ∷ 2 ∷ 3 ∷ []) ≡ 6
sumList-test = refl

_++_ : {A : Type} → List A → List A → List A
_++_ = {!!}
infixr 5 _++_

++-test : 3 ∷ 2 ∷ [] ++ 1 ∷ 4 ∷ [] ≡ 3 ∷ 2 ∷ 1 ∷ 4 ∷ []
++-test = refl

map : {A B : Type} → (A → B) → List A → List B
map = {!!}

map-test : map (_+ 2) (3 ∷ 9 ∷ []) ≡ (5 ∷ 11 ∷ [])
map-test = refl

iteList : {A B : Type} → B → (A → B → B) → List A → B
iteList n c [] = n
iteList n c (a ∷ as) = c a (iteList n c as)

-- FEL: add meg a fenti fuggvenyeket (length, ..., map) iteList segitsegevel!

-- FEL: add meg recNat-ot, es vezesd vissza iteNat-ra!

---------------------------------------------------------
-- trees
---------------------------------------------------------

-- FEL: oldd meg http://www.cs.nott.ac.uk/~psztxa/mgs.2021/datatypes.pdf -ben a 3. feladatot! (74. oldal)

---------------------------------------------------------
-- coinductive types
---------------------------------------------------------
