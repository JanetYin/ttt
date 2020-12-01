module tut.t1.gy09 where

open import lib

-------------------------------------------------
-- Natural numbers
-------------------------------------------------

pred' : ℕ → ℕ ⊎ ⊤
pred' = indℕ (λ _ → ℕ ⊎ ⊤) (inj₂ tt) (λ n _ → inj₁ n)

eq0 : ℕ → Bool
eq0 = rec true (λ _ → false)

eqℕ : ℕ → ℕ → Bool
eqℕ = rec eq0 (λ eqn m → case (pred' m) eqn (λ _ → false))

Eqℕ : ℕ → ℕ → Set
Eqℕ = λ a b → if eqℕ a b then ⊤ else ⊥

-- reflexivity
reflℕ : (a : ℕ) → Eqℕ a a
reflℕ = indℕ (λ x → Eqℕ x x) tt (λ _ e → e)

-- transport
transpℕ : (a b : ℕ) → Eqℕ a b → (P : ℕ → Set) → P a → P b
transpℕ = indℕ
  (λ a → (b : ℕ) → Eqℕ a b → (P : ℕ → Set) → P a → P b)
  (indℕ
    (λ b → Eqℕ zero b → (P : ℕ → Set) → P zero → P b)
    (λ _ _ u → u)
    (λ _ _ → exfalso))
  (λ n ih → indℕ
    (λ b → Eqℕ (suc n) b → (P : ℕ → Set) → P (suc n) → P b)
    exfalso
    (λ n' ih' e P → ih n' e (λ x → P (suc x))))

-- commutativity of equality of ℕ: use transpℕ!
sym : (a b : ℕ) → Eqℕ a b → Eqℕ b a
sym a b e = transpℕ a b e (λ x → Eqℕ x a) (reflℕ a)

-- transitivity of equality of ℕ: use transpℕ!
trans : (a b c : ℕ) → Eqℕ a b → Eqℕ b c → Eqℕ a c
trans a b c e e' = transpℕ b c e' (λ x → Eqℕ a x) e

-- congruence: use transpℕ!
cong : (f : ℕ → ℕ) → (a b : ℕ) → Eqℕ a b → Eqℕ (f a) (f b)
cong f a b e = transpℕ a b e (λ b → Eqℕ (f a) (f b)) (reflℕ (f a))

-- disjointness of different constructors of ℕ
disj : (a : ℕ) → ¬ Eqℕ zero (suc a)
disj = λ _ e → e

-- injectivity of suc
inj : (a b : ℕ) → Eqℕ a b → Eqℕ (suc a) (suc b)
inj = λ a b e → e

-- addition
_+_ : ℕ → ℕ → ℕ
_+_ = λ a b → rec b suc a
infixl 5 _+_

-- properties of addition

-- no need for indℕ
idl : (a : ℕ) → Eqℕ (0 + a) a
idl = reflℕ

-- use indℕ
idr : (a : ℕ) → Eqℕ (a + 0) a
idr = indℕ (λ a → Eqℕ (a + 0) a) (reflℕ 0) (λ _ e → e)

-- use indℕ
ass : (a b c : ℕ) → Eqℕ ((a + b) + c) (a + (b + c))
ass = λ a b c → indℕ
  (λ a → Eqℕ ((a + b) + c) (a + (b + c)))
  (reflℕ (b + c))
  (λ _ e → e)
  a

-- use indℕ
suc+ : (a b : ℕ) → Eqℕ (suc a + b) (a + suc b)
suc+ = λ a b → indℕ
  (λ a → Eqℕ (suc a + b) (a + suc b))
  (reflℕ (1 + b))
  (λ _ e → e)
  a

-- use indℕ, trans, suc+
comm : (a b : ℕ) → Eqℕ (a + b) (b + a)
comm = λ a b → indℕ
  (λ a → Eqℕ (a + b) (b + a))
  (sym (b + 0) b (idr b))
  (λ n e → trans (suc n + b) (suc b + n) (b + suc n) e (suc+ b n))
  a

_*_ : ℕ → ℕ → ℕ
_*_ = λ a b → rec 0 (_+_ b) a
infixl 7 _*_

-- laws for muliplication

-- use indℕ
idl* : (a : ℕ) → Eqℕ (1 * a) a
idl* = indℕ (λ a → Eqℕ (1 * a) a) (reflℕ 0) (λ _ e → e)

-- use indℕ
idr* : (a : ℕ) → Eqℕ (a * 1) a
idr* = indℕ (λ a → Eqℕ (a * 1) a) (reflℕ 0) (λ _ e → e)

-- no need for indℕ
nulll : (a : ℕ) → Eqℕ (0 * a) 0
nulll = λ _ → reflℕ 0

-- use indℕ
nullr : (a : ℕ) → Eqℕ (a * 0) 0
nullr = indℕ (λ a → Eqℕ (a * 0) 0) (reflℕ 0) (λ _ e → e)

-- use indℕ, trans, cong, sym, ass
distr : (a b c : ℕ) → Eqℕ ((a + b) * c) (a * c + b * c)
distr = λ a b c → indℕ
  (λ a → Eqℕ ((a + b) * c) (a * c + b * c))
  (reflℕ (b * c))
  (λ n e → trans
    ((suc n + b) * c)
    (c + (n * c + b * c))
    (suc n * c + b * c)
    (cong (_+_ c) ((n + b) * c) (n * c + b * c) e)
    (sym (suc n * c + b * c) (c + (n * c + b * c)) (ass c (n * c) (b * c))))
  a

-- use indℕ, trans, distr, cong
ass* : (a b c : ℕ) → Eqℕ ((a * b) * c) (a * (b * c))
ass* = λ a b c → indℕ
  (λ a → Eqℕ ((a * b) * c) (a * (b * c)))
  tt
  (λ n e → trans
    (suc n * b * c)
    (b * c + (n * b) * c)
    (suc n * (b * c))
    (distr b (n * b) c)
    (cong (_+_ (b * c)) ((n * b) * c) (n * (b * c)) e))
  a

-- use indℕ, trans, sym, ass, cong, comm
suc* : (a b : ℕ) → Eqℕ (a + a * b) (a * suc b)
suc* = λ a b → indℕ
  (λ a → Eqℕ (a + a * b) (a * suc b))
  (reflℕ 0)
  (λ n e → trans
    (suc n + suc n * b)
    (suc b + (n + n * b))
    (suc n * suc b)
    (trans
      (n + (b + n * b))
      ((n + b) + n * b)
      (b + (n + n * b))
      (sym (n + b + n * b) (n + (b + n * b)) (ass n b (n * b)))
      (trans
        ((n + b) + n * b)
        ((b + n) + n * b)
        (b + (n + n * b))
        (cong (_+ (n * b)) (n + b) (b + n) (comm n b))
        (ass b n (n * b))))
    (cong (_+_ (suc b)) (n + n * b) (n * suc b) e))
  a

-- use indℕ, nullr, trans, suc*
comm* : (a b : ℕ) → Eqℕ (a * b) (b * a)
comm* = λ a b → indℕ
  (λ a → Eqℕ (a * b) (b * a))
  (sym (b * zero) zero (nullr b))
  (λ n e → trans
    (suc n * b)
    (b + b * n)
    (b * suc n)
    (cong (_+_ b) (n * b) (b * n) e)
    (suc* b n))
  a

-- left distributivity: use comm* and distr
distl : (a b c : ℕ) → Eqℕ (a * (b + c)) (a * b + a * c)
distl = {!!}

-------------------------------------------------
-- building on the above
-------------------------------------------------

p4 : (x y : ℕ) → Eqℕ ((x + (y + zero)) + x) (2 * x + y)
p4 x y = trans (x + (y + zero) + x) (x + y + x) (2 * x + y)
               (cong (λ t → x + t + x) _ _ (idr y))
               (trans (x + y + x) (x + x + y) (x + (x + 0) + y)
                      (trans (x + y + x) (x + (y + x)) _
                             (ass x y x)
                             (trans (x + (y + x)) (x + (x + y)) (x + x + y)
                                    (cong (λ t → x + t) _ _ (comm y x))
                                    (sym (x + x + y) _ (ass x x y))))
                      (cong (λ t → x + t + y) _ _ (sym _ x (idr x) )))

p3 : (a b : ℕ) → Eqℕ (a + a + b + a * 0) (2 * a + b)
p3 a b = trans (a + a + b + a * 0) (a + a + b) (2 * a + b)
               (trans (a + a + b + a * 0) (a + a + b + 0) (a + a + b)
                      (cong (λ t → a + a + b + t) _ _ (nullr a))
                      (idr (a + a + b)))
               (cong (λ t → a + t + b) _ _ (sym (a + 0) a (idr a))) 


p2 : (a b c : ℕ) → Eqℕ (c * (b + 1 + a)) (a * c + b * c + c)
p2 a b c = trans (c * (b + 1 + a)) (c * (b + 1) + c * a ) _
                  (distl c (b + 1) a)
                  (trans (c * (b + 1) + c * a) (c * b + c * 1 + c * a) (a * c + b * c + c)
                         (cong (λ t → t + c * a) (c * (b + 1)) (c * b + c * 1) (distl c b 1) )
                         (trans (c * b + c * 1 + c * a) (c * b + c * 1 + a * c) _
                                (cong (λ t → c * b + c * 1 + t) _ _ (comm* c a))
                                (trans (c * b + c * 1 + a * c) (c * b + c + a * c) _
                                       (cong (λ t → c * b + t + a * c)  _ _ (idr* c))
                                       (trans (c * b + c + a * c) (b * c + c + a * c) _
                                              (cong (λ t → t + c + a * c) (c * b) (b * c) (comm* c b) )
                                              (trans (b * c + c + a * c) (a * c + (b * c + c)) _
                                                     (comm (b * c + c) _) (sym (a * c + b * c + c) _ (ass (a * c) (b * c) c)))))))


_^_ : ℕ → ℕ → ℕ
a ^ n = rec 1 (_* a) n
infixl 9 _^_

p1 : (a b : ℕ) → Eqℕ ((a + b) ^ 2) (a ^ 2 + 2 * a * b + b ^ 2)
p1 = {!!}

-------------------------------------------------
-- laws about exponentiation
-------------------------------------------------

0^ : (n : ℕ) → Eqℕ (0 ^ (suc n)) 0
0^ n = nullr (0 ^ n)

^0 : (a : ℕ) → Eqℕ (a ^ 0) 1
^0 = λ _ → tt

1^ : (n : ℕ) → Eqℕ (1 ^ n) 1
1^ = indℕ _ tt λ n h → trans (1 ^ n * 1) (1 ^ n) 1
                        (idr* (1 ^ n))
                        h

^1 : (a : ℕ) → Eqℕ (a ^ 1) a
^1 = idr*

^+ : (a m n : ℕ) → Eqℕ (a ^ (m + n)) (a ^ m * a ^ n)
^+ = {!!}

^* : (a m n : ℕ) → Eqℕ (a ^ (m * n)) ((a ^ m) ^ n)
^* = {!!}

*^ : (a b n : ℕ) → Eqℕ ((a * b) ^ n) (a ^ n * b ^ n)
*^ = {!!}

-------------------------------------------------
-- leq
-------------------------------------------------

_≤_ : ℕ → ℕ → Set
zero  ≤ y     = ⊤
suc x ≤ zero  = ⊥
suc x ≤ suc y = x ≤ y

ex : 3 ≤ 100
ex = tt

refl≤ : (x : ℕ) → x ≤ x
refl≤ zero = tt
refl≤ (suc n) = refl≤ n

trans≤ : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
trans≤ zero    y       z       e e' = tt
trans≤ (suc x) (suc y) (suc z) e e' = trans≤ x y z e e'

≤dec : (x y : ℕ) → x ≤ y ⊎ y ≤ x
≤dec zero y = inj₁ tt
≤dec (suc x) zero = inj₂ tt
≤dec (suc x) (suc y) = ≤dec x y

_<_ : ℕ → ℕ → Set
x < y = suc x ≤ y

-- C-c, C-c
≤-antisym : (x y : ℕ) → x ≤ y → y ≤ x → Eqℕ x y
≤-antisym zero zero e e' = tt
≤-antisym (suc x) (suc y) e e' = ≤-antisym x y e e'

≤dec' : (x y : ℕ) → x < y ⊎ Eqℕ x y ⊎ y < x
≤dec' zero zero = inj₂ (inj₁ tt)
≤dec' zero (suc y) = inj₁ tt
≤dec' (suc x) zero = inj₂ (inj₂ tt)
≤dec' (suc x) (suc y) = ≤dec' x y

+≤ : (x y a : ℕ) → (a + x) ≤ (a + y) ↔ x ≤ y
+≤ x y zero = (λ x → x) , λ x → x
+≤ x y (suc a) = +≤ x y a
-- suc a + x = suc (a + x)
-- suc (a + x) ≤ suc (a + y) = (a + x) ≤ (a + y)

1+*≤ : (x y a : ℕ) → (suc a * x) ≤ (suc a * y) ↔ x ≤ y
1+*≤ x y zero = (λ e → transpℕ (1 * y) y (idl* y) (λ t → x ≤ t) (transpℕ (1 * x) x (idl* x) (λ t → t ≤ (1 * y)) e))
                , {!!}
1+*≤ x y (suc a) = {!!}
-- (a b : ℕ) → Eqℕ a b → (P : ℕ → Set) → P a → P b

--_*_ = λ a b → rec 0 (_+_ b) a
-- 1 * x = rec 0 (x +_) 1 = x + 0
-- 1 * y = y + 0

¬*≤ : ¬ ((x y a : ℕ) → (a * x) ≤ (a * y) ↔ x ≤ y)
¬*≤ t = proj₁ (t 10 5 0) tt

