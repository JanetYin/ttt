
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

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero  * b = zero
suc a * b = a * b + b

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

-- természetes szám műveletek folytatás
------------------------------------------------------------

0* : (a : ℕ) → ℕEq (0 * a) 0
0* a = {!!}

*0 : (a : ℕ) → ℕEq (a * 0) 0
*0 a = {!!}

*+-distrib : (a b c : ℕ) → ℕEq (a * (b + c)) (a * b + a * c)
*+-distrib a b c = {!!}

*-assoc : (a b c : ℕ) → ℕEq ((a * b) * c) (a * (b * c))
*-assoc a b c = {!!}

*-comm : (a b : ℕ) → ℕEq (a * b) (b * a)
*-comm a b = {!!}

-- Σ típusok folytatás
------------------------------------------------------------

f4 : (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a)  ↔ Σ A P ⊎ Σ A Q
f4 = {!!}

f5 : (A : Set)(P : A → Set) → (Σ A λ a → ¬ P a) → ¬ ((a : A) → P a)
f5 = {!!}

f6 : (A : Set)(P : A → Set) → (¬ Σ A λ a → P a) ↔ ((a : A) → ¬ P a)
f6 = {!!}

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

ex : 3 ≤ 100
ex = {!!}

refl≤ : (x : ℕ) → x ≤ x
refl≤ = {!!}

trans≤ : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
trans≤ = {!!}

≤dec : (x y : ℕ) → x ≤ y ⊎ y ≤ x
≤dec x y = {!!}
