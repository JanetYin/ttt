module gy14 where

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
-- less than or equal

_≤_ : ℕ → ℕ → Set
zero  ≤ y     = ⊤
suc x ≤ zero  = ⊥
suc x ≤ suc y = x ≤ y

refl≤ : (x : ℕ) → x ≤ x
refl≤ zero = tt
refl≤ (suc x) = refl≤ x

trans≤ : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
trans≤ zero zero zero = λ _ _ → tt
trans≤ zero zero (suc z) = λ _ _ → tt
trans≤ zero (suc y) zero = λ _ _ → tt
trans≤ zero (suc y) (suc z) = λ _ _ → tt
trans≤ (suc x) zero zero = λ z _ → z
trans≤ (suc x) zero (suc z) = λ t _ → exfalso t
trans≤ (suc x) (suc y) zero = λ _ z → z
trans≤ (suc x) (suc y) (suc z) = trans≤ x y z

≤dec : (x y : ℕ) → x ≤ y ⊎ y ≤ x
≤dec zero zero = inj₁ tt
≤dec zero (suc y) = inj₁ tt
≤dec (suc x) zero = inj₂ tt
≤dec (suc x) (suc y) = ≤dec x y

_<_ : ℕ → ℕ → Set
x < y = suc x ≤ y

-----------------------------------------------------------------
--- Gyakorlat
-----------------------------------------------------------------

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
A ^ zero  = ⊤
A ^ suc x = A × (A ^ x)

-- Define the same with primrec!
_^'_ : Set → ℕ → Set
_^'_ = {!!}

exVec : Bool ^ 3
exVec = {!false , true , true , tt!}

exVec' : ℕ ^ 4
exVec' = {!1 , 2 , 3 , 4 , tt!}

⊤s : (n : ℕ) → ⊤ ^ n
⊤s = {!!}

------------------
_∧_ : Bool → Bool → Bool
_∧_ = {!!}

eqn : ℕ → ℕ → Bool
eqn zero zero = true
eqn zero (suc y) = false
eqn (suc x) zero = false
eqn (suc x) (suc y) = eqn x y

eq^ : (l : ℕ) → ℕ ^ l → ℕ ^ l → Bool
eq^ = {!!}

toSet : Bool → Set
toSet = λ b → if b then ⊤ else ⊥

Eq^ : (l : ℕ) → ℕ ^ l → ℕ ^ l → Set
Eq^ = {!!}


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

map : (A B : Set)(n : ℕ)(f : A → B) → A ^ n → B ^ n
map = {!!}

not : Bool → Bool
not true = false
not false = true

even : ℕ → Bool
even zero = true
even (suc n) = not (even n)

-- alternate 5 = true , false , true , false , true , tt
alternate : (n : ℕ) → Bool ^ n
alternate = {!!}

++ : (A : Set)(n m : ℕ) → A ^ n → A ^ m → A ^ (n + m)
++ = {!!}

filter : (A : Set)(n : ℕ)(f : A → Bool) → A ^' n → Σ ℕ λ m → A ^' m
filter = {!!}
-- where!

-- returns the m'th element
!! : (A : Set)(n : ℕ) → A ^' n → (m : ℕ) → m < n → A
!! = {!!}

-- returns inj₁ index or inj₂ tt if it is not in the list
lookup'' : (n : ℕ)(x : ℕ)(ys : ℕ ^' n) → ℕ ⊎ ⊤
lookup'' = {!!}

=dec : (x : ℕ)(y : ℕ) → Eqn x y ⊎ ¬ Eqn x y
=dec = {!!}

lookup' : (n : ℕ)(x : ℕ)(ys : ℕ ^' n) → (Σ ℕ λ i → Σ (i < n) λ p → Eqn (!! ℕ n ys i p) x) ⊎ ⊤
lookup' = {!!}

lookup : (n : ℕ)(x : ℕ)(xs : ℕ ^' n) → Decidable (Σ ℕ λ i → Σ (i < n) λ p → Eqn (!! ℕ n xs i p) x)
lookup = {!!}

insert : ℕ → (l : ℕ) → ℕ ^ l → ℕ ^ (suc l)
insert = {!!}

insert-test1 : Eq^ 5 (insert 3 4 (1 , 2 , 4 , 5 , tt)) (1 , 2 , 3 , 4 , 5 , tt)
insert-test1 = {!!}

insert-test2 : Eq^ 5 (insert 0 4 (1 , 2 , 4 , 5 , tt)) (0 , 1 , 2 , 4 , 5 , tt)
insert-test2 = {!!}

insert-test3 : Eq^ 5 (insert 1 4 (1 , 2 , 4 , 5 , tt)) (1 , 1 , 2 , 4 , 5 , tt)
insert-test3 = {!!}

insert-test4 : Eq^ 5 (insert 10 4 (1 , 2 , 4 , 5 , tt)) (1 , 2 , 4 , 5 , 10 , tt)
insert-test4 = {!!}

sort : (l : ℕ) → ℕ ^ l → ℕ ^ l
sort zero _ = tt
sort (suc l) (x , xs) = insert x l (sort l xs)

sort-test5 : Eq^ 5 (sort 5 (3 , 2 , 1 , 5 , 4 , tt)) (1 , 2 , 3 , 4 , 5 , tt)
sort-test5 = {!!}

sort-test6 : Eq^ 5 (sort 5 (2 , 2 , 1 , 4 , 4 , tt)) (1 , 2 , 2 , 4 , 4 , tt)
sort-test6 = {!!}

Ordered : ℕ → (l : ℕ) → ℕ ^ l → Set
Ordered b zero tt          = ⊤
Ordered b (suc l) (x , xs) = b ≤ x × Ordered x l xs

-- examples:

ord-test1 : Ordered 3 4 (4 , 7 , 9 , 10 , tt)
ord-test1 = tt , tt , tt , tt , tt

ord-test1a : Ordered 3 4 (4 , 4 , 9 , 10 , tt)
ord-test1a = tt , tt , tt , tt , tt

ord-test2 : ¬ Ordered 0 2 (2 , 1 , tt)
ord-test2 = λ z → proj₁ (proj₂ z)

ord-test3 : ¬ Ordered 1 2 (0 , 0 , tt)
ord-test3 = proj₁

ins-ord : (l : ℕ)(xs : ℕ ^ l)(b : ℕ) → Ordered b l xs → (y : ℕ) → b ≤ y →
  Ordered b (suc l) (insert y l xs)
ins-ord = {!!}

sort-ord : (l : ℕ)(xs : ℕ ^ l) → Ordered 0 l (sort l xs)
sort-ord = {!!}

∈ : (y : ℕ)(l : ℕ)(xs : ℕ ^ l) → Set
∈ y zero    tt       = ⊥
∈ y (suc l) (x , xs) = Eqn y x ⊎ ∈ y l xs

-- examples
 
∈-test1 : ∈ 3 4 (6 , 4 , 3 , 2 , tt)
∈-test1 = {!!}

∈-test2a : ∈ 3 4 (6 , 4 , 3 , 3 , tt)
∈-test2a = {!!}

∈-test2b : ∈ 3 4 (6 , 4 , 3 , 3 , tt)
∈-test2b = {!!}

∈-test3 : ¬ ∈ 3 4 (1 , 1 , 1 , 1 , tt)
∈-test3 = {!!}

ins-∈ : (y : ℕ)(l : ℕ)(xs : ℕ ^ l) → ∈ y (suc l) (insert y l xs)
ins-∈ = {!!}

ins-other : (y z l : ℕ)(xs : ℕ ^ l) → ∈ y l xs → ∈ y (suc l) (insert z l xs)
ins-other = {!!}

sort-∈ : (y : ℕ)(l : ℕ)(xs : ℕ ^ l) → ∈ y l xs → ∈ y l (sort l xs)
sort-∈ = {!!}
