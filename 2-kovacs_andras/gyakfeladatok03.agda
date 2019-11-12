
open import lib

-- ℕ-egyenlőség
------------------------------------------------------------

ℕEq : ℕ → ℕ → Set
ℕEq zero   zero     = ⊤
ℕEq zero   (suc m)  = ⊥
ℕEq (suc n) zero    = ⊥
ℕEq (suc n) (suc m) = ℕEq n m

ℕ-refl : (n : ℕ) → ℕEq n n
ℕ-refl zero    = tt
ℕ-refl (suc n) = ℕ-refl n

ℕ-sym : (n m : ℕ) → ℕEq n m → ℕEq m n
ℕ-sym zero    zero    eq = tt
ℕ-sym (suc n) (suc m) eq = ℕ-sym n m eq

ℕ-trans : (n m k : ℕ) → ℕEq n m → ℕEq m k → ℕEq n k
ℕ-trans zero    zero    zero    eq1 eq2 = tt
ℕ-trans (suc n) (suc m) (suc k) eq1 eq2 = ℕ-trans n m k eq1 eq2

ℕ-subst : (P : ℕ → Set)(n m : ℕ) → ℕEq n m → P n → P m
ℕ-subst P zero    zero    eq pn = pn
ℕ-subst P (suc n) (suc m) eq pn = ℕ-subst (λ x → P (suc x)) n m eq pn

------------------------------------------------------------

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero + b = b
suc a + b = suc (a + b)

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero  * b = zero
suc a * b = a * b + b

------------------------------------------------------------

0+ : (a : ℕ) → ℕEq (0 + a) a
0+ a = {!!}

+0 : (a : ℕ) → ℕEq (a + 0) a
+0 a = {!!}

+suc : (a b : ℕ) → ℕEq (a + suc b) (suc (a + b))
+suc a b = {!!}

+-assoc : (a b c : ℕ) → ℕEq ((a + b) + c) (a + (b + c))
+-assoc a b c = {!!}

+-comm : (a b : ℕ) → ℕEq (a + b) (b + a)
+-comm a b = {!!}

0* : (a : ℕ) → ℕEq (0 * a) 0
0* a = {!!}

*0 : (a : ℕ) → ℕEq (a * 0) 0
*0 a = {!!}

*-assoc : (a b c : ℕ) → ℕEq ((a * b) * c) (a * (b * c))
*-assoc a b c = {!!}

*-comm : (a b : ℕ) → ℕEq (a * b) (b * a)
*-comm a b = {!!}

*+-distrib : (a b c : ℕ) → ℕEq (a * (b + c)) (a * b + a * c)
*+-distrib a b c = {!!}
