
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
0* a = tt

*0 : (a : ℕ) → ℕEq (a * 0) 0
*0 zero = tt
*0 (suc a) =
  ℕ-trans (a * 0 + 0) (a * 0) 0
          (+0 (a * 0))
          (*0 a)

1* : ∀ a → ℕEq (1 * a) a
1* a = ℕ-refl a

*1 : ∀ a → ℕEq (a * 1) a
*1 zero = tt
*1 (suc a) =
   ℕ-trans (a * 1 + 1) (1 + a * 1) (suc a)
            (+-comm (a * 1) 1)
            (*1 a)

*+-distrib :
   (a b c : ℕ) → ℕEq (a * (b + c)) (a * b + a * c)
*+-distrib zero b c = tt
*+-distrib (suc a) b c =

   let lem = ℕ-cong (λ x → x + (b + c))
            (a * (b + c)) (a * b + a * c)
            (*+-distrib a b c)

       lem2 = ℕ-sym
           (a * b + b + (a * c + c))
           (a * b + (b + (a * c + c)))
           (+-assoc (a * b) b (a * c + c))

   in ℕ-trans (a * (b + c) + (b + c))
              (a * b + a * c + (b + c))
              (a * b + b + (a * c + c))
              lem
              (ℕ-trans
                  (a * b + a * c + (b + c))
                  (a * b + (b + (a * c + c)))
                  (a * b + b + (a * c + c))
                  (ℕ-trans
                    (a * b + a * c + (b + c))
                    (a * b + (a * c + (b + c)))
                    (a * b + (b + (a * c + c)))
                    (+-assoc (a * b) (a * c) (b + c))
                    (ℕ-cong
                      (λ x → a * b + x)
                      (a * c + (b + c))
                      (b + (a * c + c))
                      (ℕ-trans
                        (a * c + (b + c))
                        (a * c + b + c)
                        (b + (a * c + c))
                        (ℕ-sym (a * c + b + c) (a * c + (b + c))
                               (+-assoc (a * c) b c))
                        (ℕ-trans
                          (a * c + b + c)
                          (b + a * c + c)
                          (b + (a * c + c))
                          (ℕ-cong
                            (λ x → x + c)(a * c + b) (b + a * c)
                            (+-comm (a * c) b))
                            (+-assoc b (a * c) c)))))
                  lem2)

*-assoc : (a b c : ℕ) → ℕEq ((a * b) * c) (a * (b * c))
*-assoc a b c = {!!}

*-comm : (a b : ℕ) → ℕEq (a * b) (b * a)
*-comm a b = {!!}
