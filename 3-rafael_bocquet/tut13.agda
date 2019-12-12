module tut13 where
open import lib

-- Emacs key bindings (C = Ctrl, M = Alt):
-- C-x C-f : create or open a file
-- C-x C-s : save a file
-- C-x C-c : close Emacs
-- M-w : Copy
-- C-y : Paste
--
-- Agda-mode key bindings:
-- C-c C-l : Typecheck
-- C-c C-n : Evaluate
-- C-c C-, : Check the type of a hole
-- C-c C-. : Check the type of a hole, and the type of the expresion in the hole
-- C-u C-u C-c C-, : Type of the hole fully normalised
-- C-u C-u C-c C-. : Type of the hole and expression, fully normalised
-- C-u C-c C-, : Type of the hole not normalised at all
-- C-u C-c C-. : Type of the hole and expression, not normalised at all
-- C-c C-SPACE : Fill a hole
-- C-c C-r : Try to automatically fill a hole
-- C-c C-c : Case split.
-- C-c C-a : Try to fill a hole automatically
--
-- Symbols: λ = \lambda
--          × = \times
--          → = \r
--          ₁ = \_1
--          ₂ = \_2
--          ⊎ = \u+
--          ≤ = \le
--          ↔ = \<->
--          ⊤ = \top
--          ⊥ = \bot
--          ¬ = \neg
--          ≡ = \==
--          ∎ = \qed

infix 3 _≤_
infixl 4 _+_
infixl 5 _*_

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc n + m = suc (n + m)

_*_ : ℕ → ℕ → ℕ
zero * m = zero
suc n * m = m + (n * m)

Eqn : ℕ → ℕ → Set
Eqn zero    zero = ⊤
Eqn zero    (suc y) = ⊥
Eqn (suc x) zero = ⊥
Eqn (suc x) (suc y) = Eqn x y

---

Eqn-transp : (P : ℕ → Set) (x y : ℕ) (p : Eqn x y) → P x → P y
Eqn-transp P zero zero p a = a
Eqn-transp P zero (suc y) p a = exfalso p
Eqn-transp P (suc x) zero p a = exfalso p
Eqn-transp P (suc x) (suc y) p a = Eqn-transp (λ z → P (suc z)) x y p a

Eqn-refl : (n : ℕ) → Eqn n n
Eqn-refl zero = tt
Eqn-refl (suc n) = Eqn-refl n

Eqn-sym : (a b : ℕ) → Eqn a b → Eqn b a
Eqn-sym a b x = Eqn-transp (λ y → Eqn y a) a b x (Eqn-refl a)

Eqn-trans : (a b c : ℕ) → Eqn a b → Eqn b c → Eqn a c
Eqn-trans a b c p q = Eqn-transp (λ y → Eqn a y) b c q p

Eqn-cong : (x y : ℕ) → (f : ℕ → ℕ) → Eqn x y → Eqn (f x) (f y)
Eqn-cong x y f p = Eqn-transp (λ z → Eqn (f x) (f z)) x y p (Eqn-refl (f x))

---- Proofs about _+_

+-idr : (x : ℕ) → Eqn (x + zero) x
+-idr zero = tt
+-idr (suc x) = +-idr x

+-idl : (x : ℕ) → Eqn (zero + x) x
+-idl x = Eqn-refl x

+-suc : (a b : ℕ) → Eqn (a + suc b) (suc (a + b))
+-suc zero b = Eqn-refl b
+-suc (suc a) b = +-suc a b

+-assoc : (a b c : ℕ) → Eqn ((a + b) + c) (a + (b + c))
+-assoc zero b c = Eqn-refl (b + c)
+-assoc (suc a) b c = +-assoc a b c

+-comm : (a b : ℕ) → Eqn (a + b) (b + a)
+-comm a zero = +-idr a
+-comm a (suc b) = Eqn-trans (a + suc b) (suc (a + b)) (suc (b + a)) (+-suc a b) (+-comm a b)

_≤_ : ℕ → ℕ → Set
zero  ≤ y     = ⊤
suc x ≤ zero  = ⊥
suc x ≤ suc y = x ≤ y

_<_ : ℕ → ℕ → Set
x < y = suc x ≤ y

---- Vectors

_^_ : Set → ℕ → Set
A ^ zero  = ⊤
A ^ suc x = A × A ^ x

nil : (A : Set) → A ^ 0
nil = λ A → tt

cons : (A : Set) (n : ℕ) → A → A ^ n → A ^ (suc n)
cons = λ A n x xs → x , xs

head : (A : Set) (n : ℕ) → A ^ (suc n) → A
head A n (x , xs) = x

tail : (A : Set) (n : ℕ) → A ^ (suc n) → A ^ n
tail A n (x , xs) = xs




snoc : (A : Set) (n : ℕ) → A ^ n → A → A ^ (suc n)
snoc A zero tt x = (x , tt)
snoc A (suc n) (y , xs) x = y , snoc A n xs x

-- Define equality for vectors
Eqv : (l : ℕ) → ℕ ^ l → ℕ ^ l → Set
Eqv zero tt tt = ⊤
Eqv (suc l) (x , xs) (y , ys) = Eqn x y × Eqv l xs ys

Eqv-refl : (l : ℕ) → (xs : ℕ ^ l) → Eqv l xs xs
Eqv-refl zero xs = tt
Eqv-refl (suc l) (x , xs) = Eqn-refl x , Eqv-refl l xs

-- Some functions on vectors : map, concat, reverse, lookup, filter
map : (A B : Set) (n : ℕ) (f : A → B) → A ^ n → B ^ n
map A B zero f xs = tt
map A B (suc n) f (x , xs) = f x , map A B n f xs

concat : (A : Set) (n m : ℕ) → A ^ n → A ^ m → A ^ (n + m)
concat A zero m xs ys = ys
concat A (suc n) m (x , xs) ys = x , concat A n m xs ys

reverse : (A : Set) (n : ℕ) (xs : A ^ n) → A ^ n
reverse A zero xs = tt
reverse A (suc n) (x , xs) = snoc A n (reverse A n xs) x

lookup : (A : Set) (n : ℕ) → A ^ n → (m : ℕ) → m < n → A
lookup A zero xs m p = exfalso p
lookup A (suc n) (x , xs) zero p = x
lookup A (suc n) (x , xs) (suc m) p = lookup A n xs m p

filter : (A : Set) (n : ℕ) (f : A → Bool) → A ^ n → Σ ℕ λ m → A ^ m
filter A zero f xs = zero , tt
filter A (suc n) f (x , xs) = let (m , ys) = filter A n f xs
                              in if f x then suc m , (x , ys) else (m , ys)

--- properties of ≤

≤-refl : (x : ℕ) → x ≤ x
≤-refl zero = tt
≤-refl (suc x) = ≤-refl x

≤-trans : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
≤-trans zero y z p q = tt
≤-trans (suc x) zero z p q = exfalso p
≤-trans (suc x) (suc y) zero p q = exfalso q
≤-trans (suc x) (suc y) (suc z) p q = ≤-trans x y z p q

≤-antisym : (x y : ℕ) → x ≤ y → y ≤ x → Eqn x y
≤-antisym zero zero p q = tt
≤-antisym zero (suc y) p q = exfalso q
≤-antisym (suc x) zero p q = exfalso p
≤-antisym (suc x) (suc y) p q = ≤-antisym x y p q

≤-dec : (x y : ℕ) → x < y ⊎ Eqn x y ⊎ y < x
≤-dec zero zero = inj₂ (inj₁ tt)
≤-dec zero (suc y) = inj₁ tt
≤-dec (suc x) zero = inj₂ (inj₂ tt)
≤-dec (suc x) (suc y) = ≤-dec x y

≤-equiv : (x y : ℕ) → x ≤ y ↔ Σ ℕ λ k → Eqn (k + x) y
proj₁ (≤-equiv zero y) p = y , +-idr y
proj₁ (≤-equiv (suc x) zero) p = exfalso p
proj₁ (≤-equiv (suc x) (suc y)) p = let (k , q) = proj₁ (≤-equiv x y) p
                                    in k , Eqn-trans (k + suc x) (suc k + x) (suc y) (+-suc k x) q
proj₂ (≤-equiv zero y) (k , p) = tt
proj₂ (≤-equiv (suc x) zero) (k , p) = exfalso (Eqn-trans (suc k + x) (k + suc x) zero (Eqn-sym (k + suc x) (suc k + x) (+-suc k x)) p)
proj₂ (≤-equiv (suc x) (suc y)) (k , p) = let r = proj₂ (≤-equiv x y) (k , Eqn-trans (suc k + x) (k + suc x) (suc y) (Eqn-sym (k + suc x) (suc k + x) (+-suc k x)) p)
                                          in r

+≤ : (x y a : ℕ) → a + x ≤ a + y ↔ x ≤ y
proj₁ (+≤ x y zero) p = p
proj₁ (+≤ x y (suc a)) p = proj₁ (+≤ x y a) p
proj₂ (+≤ x y zero) p = p
proj₂ (+≤ x y (suc a)) p = proj₂ (+≤ x y a) p

≤-Eqn : (x y : ℕ) → Eqn x y → x ≤ y
≤-Eqn zero zero e = tt
≤-Eqn (suc x) (suc y) e = ≤-Eqn x y e

¬*≤ : ¬ ((x y a : ℕ) → a * x ≤ a * y ↔ x ≤ y)
¬*≤ f = proj₁ (f 2 1 0) tt

---- Insertion sort

insert : ℕ → (l : ℕ) → ℕ ^ l → ℕ ^ (suc l)
insert y l xs = {!!}

sort : (l : ℕ) → ℕ ^ l → ℕ ^ l
sort l xs = {!!}

Ordered : ℕ → (l : ℕ) → ℕ ^ l → Set
Ordered b zero tt          = ⊤
Ordered b (suc l) (x , xs) = b ≤ x × Ordered x l xs

insert-ord : (l : ℕ)(xs : ℕ ^ l)(b : ℕ)
           → Ordered b l xs
           → (y : ℕ) → b ≤ y
           → Ordered b (suc l) (insert y l xs)
insert-ord = {!!}

sort-ord : (l : ℕ) (xs : ℕ ^ l) → Ordered 0 l (sort l xs)
sort-ord l xs = {!!}

---- Minimum & maximum

min : ℕ → ℕ → ℕ
min = {!!}

max : ℕ → ℕ → ℕ
max = {!!}

minimum : (l : ℕ) → ℕ ^ (suc l) → ℕ
minimum = {!!}

maximum : (l : ℕ) → ℕ ^ (suc l) → ℕ
maximum = {!!}

min≤max : (a b : ℕ) → min a b ≤ max a b
min≤max = {!!}

minimum≤maximum : (l : ℕ) (xs : ℕ ^ (suc l)) → minimum l xs ≤ maximum l xs
minimum≤maximum = {!!}
