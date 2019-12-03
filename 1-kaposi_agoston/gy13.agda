module gy13 where

open import lib

Decidable : Set → Set
Decidable = λ A → A ⊎ ¬ A

-- equality for ℕ
Eqn : ℕ → ℕ → Set
Eqn zero zero = ⊤
Eqn zero (suc y) = ⊥
Eqn (suc x) zero = ⊥
Eqn (suc x) (suc y) = Eqn x y

infixl 4 _+_
infixl 5 _*_

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

_*_ : ℕ → ℕ → ℕ
zero * y = zero
suc x * y = y + x * y


refln : (n : ℕ) → Eqn n n
refln = λ n → indℕ (λ n → Eqn n n) tt (λ _ e → e) n

transport : (P : ℕ → Set)(x y : ℕ) → Eqn x y → P x → P y
transport P zero zero e px = px
transport P (suc x) zero e px = exfalso e
transport P zero (suc y) e px = exfalso e
transport P (suc x) (suc y) e px = transport (λ n → P (suc n)) x y e px

sym : (x y : ℕ) → Eqn x y → Eqn y x
sym = λ x y e → transport (λ n → Eqn n x) x y e (refln x) 

trans : (x y z : ℕ) → Eqn x y → Eqn y z → Eqn x z
trans = λ x y z exy eyz → transport (λ n → Eqn x n) y z eyz exy 

cong : (f : ℕ → ℕ)(x y : ℕ) → Eqn x y → Eqn (f x) (f y)
cong = λ f x y exy → transport (λ n → Eqn (f x) (f n)) x y exy (refln (f x))

idl : (x : ℕ) → Eqn (zero + x) x
idl zero = tt
idl (suc x) = refln x

idr : (x : ℕ) → Eqn (x + zero) x
idr zero = tt
idr (suc x) = idr x

ass+ : (x y z : ℕ) → Eqn ((x + y) + z) (x + (y + z))
ass+ zero y z = refln (y + z)
ass+ (suc x) y z = ass+ x y z

comm+-lemm : (x y : ℕ) → Eqn (suc (x + y)) (x + suc y)
comm+-lemm zero zero = tt
comm+-lemm zero (suc y) = refln y
comm+-lemm (suc x) zero = comm+-lemm x zero
comm+-lemm (suc x) (suc y) = comm+-lemm x (suc y)

comm+ : (x y : ℕ) → Eqn (x + y) (y + x)
comm+ zero zero = tt
comm+ zero (suc y) = comm+ zero y
comm+ (suc x) zero = comm+ x zero
comm+ (suc x) (suc y) =
  trans
    (x + suc y)
    (suc (x + y))
    (y + suc x)
    (sym (suc x + y) (x + suc y) (comm+-lemm x y))
    (comm+ (suc x) y)

-- Gyakorlat:

¬3=4 : ¬ Eqn 3 4
¬3=4 = {!!}

¬inv : ¬ ((x : ℕ) → Σ ℕ λ x⁻¹ → Eqn (x + x⁻¹) 0)
¬inv = {!!}

lem10 : ¬ ((x y : ℕ) → Eqn (x + x) (x + y))
lem10 = {!!}

lem11 : ¬ ((x : ℕ) → Eqn (x + x) x)
lem11 = {!!}

zerol* : (n : ℕ) → Eqn (zero * n) zero
zerol* = {!!}

zeror* : (n : ℕ) → Eqn (n * zero) zero
zeror* = {!!}

idl* : (n : ℕ) → Eqn (1 * n) n
idl* = {!!}

idr* : (n : ℕ) → Eqn (n * 1) n
idr* = {!!}

distr  : (x y z : ℕ) → Eqn (x * (y + z)) (x * y + x * z)
distr = {!!}

comm*-lemma : (x y : ℕ) → Eqn (y + y * x) (y * suc x)
comm*-lemma = {!!}

comm* : (x y : ℕ) → Eqn (x * y) (y * x)
comm* = {!!}

distrl : (x y z : ℕ) → Eqn ((x + y) * z) (x * z + y * z)
distrl = {!!}

ass* : (x y z : ℕ) → Eqn ((x * y) * z) (x * (y * z))
ass* = {!!}

-- less than or equal

_≤_ : ℕ → ℕ → Set
zero  ≤ y     = ⊤
suc x ≤ zero  = ⊥
suc x ≤ suc y = x ≤ y

ex : 3 ≤ 100
ex = {!!}

refl≤ : (x : ℕ) → x ≤ x
refl≤ = {!!}

trans≤ : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
trans≤ = {!!}

≤dec : (x y : ℕ) → x ≤ y ⊎ y ≤ x
≤dec = {!!}

_<_ : ℕ → ℕ → Set
x < y = suc x ≤ y

≤-antisym : (x y : ℕ) → x ≤ y → y ≤ x → Eqn x y
≤-antisym = {!!}

≤dec' : (x y : ℕ) → x < y ⊎ Eqn x y ⊎ y < x
≤dec' = {!!}

+≤ : (x y a : ℕ) → (a + x) ≤ (a + y) ↔ x ≤ y
+≤ = {!!}

1+*≤ : (x y a : ℕ) → (suc a * x) ≤ (suc a * y) ↔ x ≤ y
1+*≤ = {!!}


¬*≤ : ¬ ((x y a : ℕ) → (a * x) ≤ (a * y) ↔ x ≤ y)
¬*≤ = {!!}

---------------------------------------------------------
-- Vectors
---------------------------------------------------------

_^_ : Set → ℕ → Set
A ^ zero  = {!!}
A ^ suc x = {!!}

_^'_ : Set → ℕ → Set
_^'_ = {!!}

exVec : Bool ^ 3
exVec = {!false , true , true , tt!}

exVec' : ℕ ^ 4
exVec' = {!1 , 2 , 3 , 4 , tt!}

⊤s : (n : ℕ) → ⊤ ^' n
⊤s = {!!}

------------------
_∧_ : Bool → Bool → Bool
true  ∧ true = true
_     ∧ _    = false
{-
eqn : ℕ → ℕ → Bool
eqn zero zero = true
eqn zero (suc y) = false
eqn (suc x) zero = false
eqn (suc x) (suc y) = eqn x y

eq^ : (l : ℕ) → ℕ ^ l → ℕ ^ l → Bool
eq^ zero xs ys = true
eq^ (suc l) (x , xs) (y , ys) = eqn x y ∧ eq^ l xs ys

toSet : Bool → Set
toSet = λ b → if b then ⊤ else ⊥

Eq^ : (l : ℕ) → ℕ ^ l → ℕ ^ l → Set
Eq^ l xs ys = toSet (eq^ l xs ys)
-------------------
-}
nil : (A : Set) → A ^' 0
nil = {!!}

cons : (A : Set)(n : ℕ) → A → A ^' n → A ^' (suc n)
cons = {!!}

head : (A : Set)(n : ℕ) → A ^' (suc n) → A
head = {!!}

tail : (A : Set)(n : ℕ) → A ^' (suc n) → A ^' n
tail = {!!}

numbers : (n : ℕ) → ℕ ^' n
numbers = {!!}

--numbersTest : Eq^ 3 (numbers 3) (2 , 1 , 0 , tt)
--numbersTest = {!!}

map : (A B : Set)(n : ℕ)(f : A → B) → A ^' n → B ^' n
map = {!!}

not : Bool → Bool
not true = false
not false = true

even : ℕ → Bool
even zero = true
even (suc n) = not (even n)

-- alternate 5 = true , false , true , false , true , tt
alternate : (n : ℕ) → Bool ^' n
alternate = {!!}

++ : (A : Set)(n m : ℕ) → A ^' n → A ^' m → A ^' (n + m)
++ = {!!}

filter : (A : Set)(n : ℕ)(f : A → Bool) → A ^' n → Σ ℕ λ m → A ^' m
filter A n f xs = {!!}

!! : (A : Set)(n : ℕ) → A ^' n → (m : ℕ) → m < n → A
!! = {!!}

-- returns inj₁ index or inj₂ tt if it is not in the list
lookup'' : (n : ℕ)(x : ℕ)(xs : ℕ ^' n) → ℕ ⊎ ⊤
lookup'' = {!!}

lookup' : (n : ℕ)(x : ℕ)(xs : ℕ ^' n) → (Σ ℕ λ i → Σ (i < n) λ p → Eqn (!! ℕ n xs i p) x) ⊎ ⊤
lookup' = {!!}

lookup : (n : ℕ)(x : ℕ)(xs : ℕ ^' n) → Decidable (Σ ℕ λ i → Σ (i < n) λ p → Eqn (!! ℕ n xs i p) x)
lookup = {!!}

insert : ℕ → (l : ℕ) → ℕ ^ l → ℕ ^ (suc l)
insert = {!!}

{-
insert-test1 : Eq^ 5 (insert 3 4 (1 , 2 , 4 , 5 , tt)) (1 , 2 , 3 , 4 , 5 , tt)
insert-test1 = tt

insert-test2 : Eq^ 5 (insert 0 4 (1 , 2 , 4 , 5 , tt)) (0 , 1 , 2 , 4 , 5 , tt)
insert-test2 = tt

insert-test3 : Eq^ 5 (insert 1 4 (1 , 2 , 4 , 5 , tt)) (1 , 1 , 2 , 4 , 5 , tt)
insert-test3 = tt

insert-test4 : Eq^ 5 (insert 10 4 (1 , 2 , 4 , 5 , tt)) (1 , 2 , 4 , 5 , 10 , tt)
insert-test4 = tt

sort : (l : ℕ) → ℕ ^ l → ℕ ^ l
sort zero _ = tt
sort (suc l) (x , xs) = insert x l (sort l xs)

sort-test5 : Eq^ 5 (sort 5 (3 , 2 , 1 , 5 , 4 , tt)) (1 , 2 , 3 , 4 , 5 , tt)
sort-test5 = tt

sort-test6 : Eq^ 5 (sort 5 (2 , 2 , 1 , 4 , 4 , tt)) (1 , 2 , 2 , 4 , 4 , tt)
sort-test6 = tt
-}
