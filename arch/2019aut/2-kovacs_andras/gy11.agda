
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

0+ : (a : ℕ) → ℕEq (0 + a) a
0+ a = ℕ-refl a

+0 : (a : ℕ) → ℕEq (a + 0) a
+0 zero = tt
+0 (suc a) = +0 a

+suc : (a b : ℕ) → ℕEq (a + suc b) (suc (a + b))
+suc zero b = ℕ-refl b
+suc (suc a) b = +suc a b

n-neq-sucn : (n : ℕ) → ¬ (ℕEq n (suc n))
n-neq-sucn zero p = p
n-neq-sucn (suc n) = n-neq-sucn n

+-assoc : (a b c : ℕ) → ℕEq ((a + b) + c) (a + (b + c))
+-assoc zero b c = ℕ-refl (b + c)
+-assoc (suc a) b c = +-assoc a b c

+-comm : (a b : ℕ) → ℕEq (a + b) (b + a)
+-comm zero    zero    = tt
+-comm zero    (suc b) = +-comm zero b
+-comm (suc a) zero    = +-comm a zero
+-comm (suc a) (suc b) =
  ℕ-trans (a + suc b) (suc (a + b)) (b + suc a)
          (ℕ-trans (a + suc b) (suc (b + a)) (suc (a + b))
                   (+-comm a (suc b))
                   (ℕ-sym (a + b) (b + a) (+-comm a b)))
          (+-comm (suc a) b)


-- Σ típusok folytatás
------------------------------------------------------------

-- függő típusos curry-zés
currying : {A : Set}{B : A → Set}{C : Set} → ((a : A) → B a → C) ↔ (Σ A B → C)
currying = {!!}

-- még függő típusosabb curry-zés
currying' :
    {A : Set}{B : A → Set}{C : (a : A) →  B a → Set}
  → ((a : A)(b : B a) → C a b) ↔ ((ab : Σ A B) → C (proj₁ ab) (proj₂ ab))
currying' = {!!}

-- negáció + Σ
f5 : (A : Set)(P : A → Set) → (Σ A λ a → ¬ P a) → ¬ ((a : A) → P a)
f5 = {!!}

f6 : (A : Set)(P : A → Set) → (¬ Σ A λ a → P a) ↔ ((a : A) → ¬ P a)
f6 = {!!}

-- A ⊎ B definiálása Σ típusként
f7→ : (A B : Set) → (A ⊎ B) → Σ Bool (λ b → if b then A else B)
f7→ = {!!}

f7← : (A B : Set) → Σ Bool (λ b → if b then A else B) → A ⊎ B
f7← = {!!}

-- természetes számok rendezése
------------------------------------------------------------

-- első definíció
infix 3 _≤_
_≤_ : ℕ → ℕ → Set
zero  ≤ y     = ⊤
suc x ≤ zero  = ⊥
suc x ≤ suc y = x ≤ y

infix 3 _<_
_<_ : ℕ → ℕ → Set
a < zero = ⊥
a < suc b = ℕEq a b ⊎ a < b

-- második definíció
infix 3 _≤'_
_≤'_ : ℕ → ℕ → Set
a ≤' b = (a < b) ⊎ ℕEq a b

example : 3 ≤ 100
example = {!!}

example2 : ¬ (2 ≤ 0)
example2 = {!!}

refl≤ : (x : ℕ) → x ≤ x
refl≤ = {!!}

trans≤ : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
trans≤ = {!!}

≤dec : (x y : ℕ) → x ≤ y ⊎ y ≤ x
≤dec x y = {!!}

-- vektorok
------------------------------------------------------------

_^_ : Set → ℕ → Set
A ^ zero  = ⊤
A ^ suc x = A × A ^ x

count : (n : ℕ) → ℕ ^ n
count zero = tt
count (suc n) = n , count n

Eq^ : (l : ℕ) → ℕ ^ l → ℕ ^ l → Set
Eq^ zero    tt       tt       = ⊤
Eq^ (suc l) (x , xs) (y , ys) = ℕEq x y × Eq^ l xs ys

Eq^-refl : ∀ l xs → Eq^ l xs xs
Eq^-refl l xs = {!!}

test-count : Eq^ 3 (count 3) (2 , 1 , 0 , tt)
test-count = Eq^-refl 3 (count 3)

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

ins-ord : (l : ℕ)(xs : ℕ ^ l)(b : ℕ) → Ordered b l xs → (y : ℕ) → b ≤ y →
  Ordered b (suc l) (insert y l xs)
ins-ord = {!!}

sort-ord : (l : ℕ)(xs : ℕ ^ l) → Ordered 0 l (sort l xs)
sort-ord l xs = {!!}
