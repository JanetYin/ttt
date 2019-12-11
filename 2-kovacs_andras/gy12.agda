
open import lib

ℕEq : ℕ → ℕ → Set
ℕEq zero   zero     = ⊤
ℕEq zero   (suc m)  = ⊥
ℕEq (suc n) zero    = ⊥
ℕEq (suc n) (suc m) = ℕEq n m

ℕ-refl : (n : ℕ) → ℕEq n n
ℕ-refl zero    = tt
ℕ-refl (suc n) = ℕ-refl n

ℕ-sym : (n m : ℕ) → ℕEq n m → ℕEq m n
ℕ-sym zero zero eq = tt
ℕ-sym (suc n) (suc m) eq = ℕ-sym n m eq

ℕ-trans : (n m k : ℕ) → ℕEq n m → ℕEq m k → ℕEq n k
ℕ-trans zero zero zero eq1 eq2 = tt
ℕ-trans (suc n) (suc m) (suc k) eq1 eq2 =
  ℕ-trans n m k eq1 eq2

ℕ-subst : (P : ℕ → Set)(n m : ℕ) → ℕEq n m → P n → P m
ℕ-subst P zero zero eq pn = pn
ℕ-subst P (suc n) (suc m) eq pn =
  ℕ-subst (λ x → P (suc x)) n m eq pn

ℕ-cong : (f : ℕ → ℕ) → (a b : ℕ) → ℕEq a b → ℕEq (f a) (f b)
ℕ-cong f zero    zero    eq = ℕ-refl (f zero)
ℕ-cong f (suc a) (suc b) eq = ℕ-cong (λ x → f (suc x)) a b eq

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero + b = b
suc a + b = suc (a + b)


-- természetes számok rendezése
------------------------------------------------------------

-- első definíció
infix 3 _≤_
_≤_ : ℕ → ℕ → Set
zero  ≤ y     = ⊤
suc x ≤ zero  = ⊥
suc x ≤ suc y = x ≤ y

-- másik definíció
infix 3 _<_
_<_ : ℕ → ℕ → Set
a < zero = ⊥
a < suc b = ℕEq a b ⊎ a < b

-- második definíció
infix 3 _≤'_
_≤'_ : ℕ → ℕ → Set
a ≤' b = (a < b) ⊎ ℕEq a b

example : 3 ≤ 100
example = tt

example2 : ¬ (2 ≤ 0)
example2 = λ p → p

refl≤ : (x : ℕ) → x ≤ x
refl≤ = {!!}

trans≤ : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
trans≤ x y z p q = {!!}

≤dec : (x y : ℕ) → x ≤ y ⊎ y ≤ x
≤dec x y = {!!}

-- extra rendezés feladatok
------------------------------------------------------------

≤-antisym : ∀ x y → x ≤ y → y ≤ x → ℕEq x y
≤-antisym x y p q = {!!}

suc¬Eq : ∀ x → ¬ (ℕEq (suc x) x)
suc¬Eq x p = {!!}

<-irrefl : ∀ x → ¬ (x < x)
<-irrefl x p = {!!}

≤'→≤ : ∀ x y → x ≤ y → x ≤' y
≤'→≤ x y p = {!!}

≤→≤' : ∀ x y → x ≤' y → x ≤ y
≤→≤' x y p = {!!}

≤'-antisym : ∀ x y → x ≤' y → y ≤' x → ℕEq x y
≤'-antisym x y p q = {!!}

-- vektorok, rendezett vektorok
------------------------------------------------------------

_^_ : Set → ℕ → Set
A ^ zero  = ⊤
A ^ suc x = A × A ^ x

count : (n : ℕ) → ℕ ^ n
count zero = tt
count (suc n) = n , count n

-- vektor egyenlőség
Eq^ : (l : ℕ) → ℕ ^ l → ℕ ^ l → Set
Eq^ zero    tt       tt       = ⊤
Eq^ (suc l) (x , xs) (y , ys) = ℕEq x y × Eq^ l xs ys

Eq^-refl : ∀ l xs → Eq^ l xs xs
Eq^-refl l xs = {!!}

Eq^-trans : ∀ l xs ys zs → Eq^ l xs ys → Eq^ l ys zs → Eq^ l xs zs
Eq^-trans l xs ys zs p q = {!!}

test-count : Eq^ 3 (count 3) (2 , 1 , 0 , tt)
test-count = Eq^-refl 3 (count 3)

-- rendezett beszúrás
insert : ℕ → (l : ℕ) → ℕ ^ l → ℕ ^ (suc l)
insert y l xs = {!!}

test-insert : Eq^ 5 (insert 3 4 (1 , 2 , 4 , 5 , tt)) (1 , 2 , 3 , 4 , 5 , tt)
test-insert = {!!}

sort : (l : ℕ) → ℕ ^ l → ℕ ^ l
sort l xs = {!!}

test-sort : Eq^ 5 (sort 5 (3 , 2 , 1 , 5 , 4 , tt)) (1 , 2 , 3 , 4 , 5 , tt)
test-sort = {!!}

Ordered : ℕ → (l : ℕ) → ℕ ^ l → Set
Ordered b zero tt          = ⊤
Ordered b (suc l) (x , xs) = b ≤ x × Ordered x l xs

ins-ord :
    (l : ℕ)(xs : ℕ ^ l)(b : ℕ)
  → Ordered b l xs
  → (y : ℕ) → b ≤ y →
  Ordered b (suc l) (insert y l xs)
ins-ord = {!!}

sort-ord : (l : ℕ)(xs : ℕ ^ l) → Ordered 0 l (sort l xs)
sort-ord l xs = {!!}
