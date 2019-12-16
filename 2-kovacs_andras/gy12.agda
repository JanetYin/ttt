
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

-- 4.feladat: aki amiatt bukik, az mégse
-- 8.feladatot beírom + jegyeket
-- utána lehet reklamálni




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
≤dec zero    zero    = inj₁ tt
≤dec zero    (suc y) = inj₁ tt
≤dec (suc x) zero    = inj₂ tt
≤dec (suc x) (suc y) = ≤dec x y

-- házi: ≤'dec : (x y : ℕ) → x ≤' y ⊎ y ≤' x

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
A ^ zero  = ⊤         -- 0-darab A-t tárol
A ^ suc x = A × A ^ x -- x + 1 darab A-t tárol

-- Haskell: replicate :: Int -> a -> [a]
replicate : (A : Set)(n : ℕ) → A → A ^ n
replicate A zero    a = tt
replicate A (suc n) a = a , (replicate A n a)
-- pl: replicate ℕ 3 3 = 3 , (3 , (3 , tt))

-- "safe" tail verzió
tail : (A : Set)(n : ℕ) → A ^ suc n → A ^ n
tail A n xs = proj₂ xs
  -- definíció: A ^ suc n = A × A ^ n

-- Haskell head :: [a] -> a  (nincs totális definíció!)
head : (A : Set)(n : ℕ) → A ^ suc n → A
head A n xs = proj₁ xs

count : (n : ℕ) → ℕ ^ n
count zero    = tt
count (suc n) = n , count n

-- vektor egyenlőség
Eq^ : (l : ℕ) → ℕ ^ l → ℕ ^ l → Set
Eq^ zero    tt       tt       = ⊤
Eq^ (suc l) (x , xs) (y , ys) = ℕEq x y × Eq^ l xs ys

Eq^-refl : ∀ l xs → Eq^ l xs xs
Eq^-refl zero    xs       = tt
Eq^-refl (suc l) (x , xs) = ℕ-refl x , Eq^-refl l xs
-- vektor refl-je, refl-ök vektorja

Eq^-trans :
  ∀ l xs ys zs → Eq^ l xs ys → Eq^ l ys zs → Eq^ l xs zs
Eq^-trans l xs ys zs p q = {!!}

test-count : Eq^ 3 (count 3) (2 , 1 , 0 , tt)
test-count = Eq^-refl 3 (count 3)

-- rendezett beszúrás
insert : ℕ → (l : ℕ) → ℕ ^ l → ℕ ^ (suc l)
insert y zero    xs       = y , tt
insert y (suc l) (x , xs) =
  case (≤dec x y) (λ p → x , insert y l xs)
                  (λ p → y , x , xs)

-- (insert 3 4 (1 , 2 , 4 , 5 , tt))
-- == 3 , 1 , 2 , 4 , 5 , tt

test-insert :
  Eq^ 5
    (insert 3 4 (1 , 2 , 4 , 5 , tt))
    (1 , 2 , 3 , 4 , 5 , tt)
test-insert = tt , tt , tt , tt , tt , tt

sort : (l : ℕ) → ℕ ^ l → ℕ ^ l
sort zero    xs       = xs
sort (suc l) (x , xs) = insert x l (sort l xs)
  -- O(n²)

test-sort : Eq^ 5 (sort 5 (3 , 2 , 1 , 5 , 4 , tt)) (1 , 2 , 3 , 4 , 5 , tt)
test-sort = tt , tt , tt , tt , tt , tt

-- Ordered b l xs
Ordered : ℕ → (l : ℕ) → ℕ ^ l → Set
Ordered b zero tt          = ⊤
Ordered b (suc l) (x , xs) = (b ≤ x) × (Ordered x l xs)

ins-ord :
    (l : ℕ)(xs : ℕ ^ l)(b : ℕ)
  → Ordered b l xs
  → (y : ℕ) → b ≤ y →
  Ordered b (suc l) (insert y l xs)
ins-ord zero    xs b ord y p = p , tt
ins-ord (suc l) (x , xs) b (q , ord) y p with ≤dec x y
... | inj₁ r = q , ins-ord l xs x ord y r
... | inj₂ r = p , r , ord

sort-ord : (l : ℕ)(xs : ℕ ^ l) → Ordered 0 l (sort l xs)
sort-ord zero    xs       = tt
sort-ord (suc l) (x , xs) =
  ins-ord l (sort l xs) 0 (sort-ord l xs) x tt

----------------------------------------
