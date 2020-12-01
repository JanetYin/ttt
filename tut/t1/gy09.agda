module tut.t1.gy09 where

open import lib

-------------------------------------------------
-- Bool
-------------------------------------------------

not : Bool → Bool
not = λ a → if a then false else true

eqb : Bool → Bool → Bool
eqb = λ a b → if a then b else not b

Eqb : Bool → Bool → Set
Eqb = λ a b → if eqb a b then ⊤ else ⊥

-- properties of Eqb

reflb : (b : Bool) → Eqb b b
reflb = {!!}

transpb : (P : Bool → Set)(a b : Bool) → Eqb a b → P a → P b
transpb = λ P a → indBool 
  (λ a → (b : Bool) → Eqb a b → P a → P b)
  (λ b → indBool (λ b → Eqb true  b → P true  → P b) (λ _ w → w) exfalso     b)
  (λ b → indBool (λ b → Eqb false b → P false → P b) exfalso     (λ _ w → w) b)
  a

-- use transpb
symb : (a b : Bool) → Eqb a b → Eqb b a
symb = {!!}

-- use transpb
transb : (a b c : Bool) → Eqb a b → Eqb b c → Eqb a c
transb = {!!}

-- every function on booleans is a congruence; use transpb to prove it
congb : (f : Bool → Bool) → (a b : Bool) → Eqb a b → Eqb (f a) (f b)
congb = λ f a b e → transpb (λ b → Eqb (f a) (f b)) a b e (reflb (f a))

-- disjointness of different constructors of Bool
disjb : ¬ Eqb true false
disjb = λ e → e

-- conjunction an disjunction

_∧_ : Bool → Bool → Bool
_∧_ = λ x y → if x then y else false
infixl 7 _∧_

_∨_ : Bool → Bool → Bool
_∨_ = λ x y → if x then true else y
infixl 5 _∨_

-- properties of _∧_ and _∨_

idl∧ : (a : Bool) → Eqb (true ∧ a)  a
idl∧ = {!!}

idr∧ : (a : Bool) → Eqb (a ∧ true)  a
idr∧ = {!!}

ass∧ : (a b c : Bool) → Eqb ((a ∧ b) ∧ c) (a ∧ (b ∧ c))
ass∧ = {!!}

comm∧ : (a b : Bool) → Eqb (a ∧ b) (b ∧ a)
comm∧ = {!!}

null∧ : (a : Bool) → Eqb (false ∧ a) false
null∧ = {!!}

idl∨ : (a : Bool) → Eqb (false ∨ a)  a
idl∨ = {!!}

idr∨ : (a : Bool) → Eqb (a ∨ false)  a
idr∨ = {!!}

ass∨ : (a b c : Bool) → Eqb ((a ∨ b) ∨ c) (a ∨ (b ∨ c))
ass∨ = {!!}

comm∨ : (a b : Bool) → Eqb (a ∨ b) (b ∨ a)
comm∨ = {!!}

null∨ : (a : Bool) → Eqb (true ∨ a) true
null∨ = {!!}

dist∧ : (a b c : Bool) → Eqb (a ∧ (b ∨ c)) (a ∧ b ∨ a ∧ c)
dist∧ = {!!}

dist∨ : (a b c : Bool) → Eqb (a ∨ (b ∧ c)) ((a ∨ b) ∧ (a ∨ c))
dist∨ = {!!}

abs∧ : (a b : Bool) → Eqb (a ∧ (a ∨ b)) a
abs∧ = {!!}

abs∨ : (a b : Bool) → Eqb (a ∨ (a ∧ b)) a
abs∨ = {!!}

-- we could also prove laws for not, like De Morgan etc.

-------------------------------------------------
-- Natural numbers
-------------------------------------------------

pred' : ℕ → ℕ ⊎ ⊤
pred' = indℕ (λ _ → ℕ ⊎ ⊤) (inj₂ tt) (λ n _ → inj₁ n)

eq0 : ℕ → Bool
eq0 = rec true (λ _ → false)

eqℕ : ℕ → ℕ → Bool
eqℕ = rec eq0 (λ eqn m → case (pred' m) eqn (λ _ → false))

-- what is the difference between eqℕ a b and Eqℕ a b?
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
               (cong (λ t → x + t + x) (y + zero ) y (idr y))
               (trans (x + y + x) (x + x + y) (2 * x + y)
                      (trans (x + y + x) (x + (y + x)) (x + x + y)
                             (ass x y x)
                             (trans (x + (y + x)) (x + (x + y)) (x + x + y)
                                    (cong (λ t → x + t) (y + x) (x + y) (comm y x))
                                    (sym (x + x + y) (x + (x + y)) (ass x x y))))
                      (cong (λ t → x + t + y) x (x + 0) (sym (x + 0) x (idr x))))
-- 2 * x = rec 0 (x +_) 2 = x + (x + 0)
-- x + (x + 0) + y

p3 : (a b : ℕ) → Eqℕ (a + a + b + a * 0) (2 * a + b)
p3 a b = trans (a + a + b + a * 0) (a + a + b + 0) (2 * a + b)
               (cong (λ t → a + a + b + t) (a * 0) 0 (nullr a))
               (trans (a + a + b + 0) (a + a + b) (2 * a + b)
                      (idr (a + a + b)  )
                      (cong (λ t → a + t + b) a (a + 0) (sym (a + 0) a (idr a))))
-- 2 * a + b = a + (a + 0) + b

p2 : (a b c : ℕ) → Eqℕ (c * (b + 1 + a)) (a * c + b * c + c)
p2 a b c = trans (c * (b + 1 + a)) (c * (b + 1) + c * a)  _
                 (distl c (b + 1) a)
                 (trans (c * (b + 1) + c * a) (c * b + c * 1 + c * a) _
                        (cong (λ t → t + c * a) (c * (b + 1)) (c * b + c * 1) (distl c b 1))
                        (trans (c * b + c * 1 + c * a) (c * b + c + c * a) _
                               (cong (λ t → c * b + t + c * a) (c * 1) c (idr* c))
                               (trans (c * b + c + c * a) (c * a + (c * b + c)) _
                                      (comm (c * b + c) (c * a))
                                      (trans (c * a + (c * b + c)) (a * c + (c * b + c)) _
                                             (cong (λ t → t + (c * b + c)) (c * a) (a * c) (comm* c a ))
                                             (trans (a * c + (c * b + c)) (a * c + (b * c + c)) _
                                                    (cong (λ t → a * c + (t + c)) (c * b) (b * c) (comm* c b))
                                                    (sym (a * c + b * c + c) (a * c + (b * c + c)) (ass (a * c) (b * c) c)))))))
-- c * (b + 1 + a)            =Eqℕ= distl
-- c * (b + 1) + c * a        =Eqℕ= distl, cong      
-- c * b + c * 1 + c * a      =Eqℕ= cong, idr*
-- c * b + c + c * a          =Eqℕ= comm
-- c * a + (c * b + c)        =Eqℕ= comm*, cong
-- a * c + (c * b + c)        =Eqℕ= comm*, cong
-- a * c + (b * c + c)        =Eqℕ= ass, sym
-- a * c + b * c + c

_^_ : ℕ → ℕ → ℕ
a ^ n = rec 1 (_* a) n
infixl 9 _^_

pow : (a n : ℕ) → ¬ (Eqℕ 0 a) ⊎ ¬ (Eqℕ 0 n) → ℕ
pow a n  _ = rec 1 (_* a) n

p1 : (a b : ℕ) → Eqℕ ((a + b) ^ 2) (a ^ 2 + 2 * a * b + b ^ 2)
p1 = {!!}

-------------------------------------------------
-- laws about exponentiation
-------------------------------------------------

0^ : (n : ℕ) → Eqℕ (0 ^ (suc n)) 0
0^ n = nullr (0 ^ n)
-- 0 ^ (suc n) = rec 1 (_* 0) (suc n) = (rec 1 (_* 0) n) * 0 = 0 ^ n

^0 : (a : ℕ) → Eqℕ (a ^ 0) 1
^0 = λ a → tt
-- a ^ 0 = rec 1 (_* a) 0 = 1

1^ : (n : ℕ) → Eqℕ (1 ^ n) 1
1^ = indℕ _
          (^0 1)
          λ n h → trans (1 ^ n * 1) (1 ^ n) 1
                        (idr* (1 ^ n))
                        h
-- 1 ^ n = rec 1 (_* 1) n = :(
-- 1 ^ suc n = 1 ^ n * 1

^1 : (a : ℕ) → Eqℕ (a ^ 1) a
^1 = idl*
-- a ^ 1 = rec 1 (_* a) 1 = 1 * a

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
ex = {!!}

refl≤ : (x : ℕ) → x ≤ x
refl≤ = {!!}

trans≤ : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
trans≤ = {!!}

≤dec : (x y : ℕ) → x ≤ y ⊎ y ≤ x
≤dec = {!!}

_<_ : ℕ → ℕ → Set
x < y = suc x ≤ y

≤-antisym : (x y : ℕ) → x ≤ y → y ≤ x → Eqℕ x y
≤-antisym = {!!}

≤dec' : (x y : ℕ) → x < y ⊎ Eqℕ x y ⊎ y < x
≤dec' = {!!}

+≤ : (x y a : ℕ) → (a + x) ≤ (a + y) ↔ x ≤ y
+≤ = {!!}

1+*≤ : (x y a : ℕ) → (suc a * x) ≤ (suc a * y) ↔ x ≤ y
1+*≤ = {!!}

¬*≤ : ¬ ((x y a : ℕ) → (a * x) ≤ (a * y) ↔ x ≤ y)
¬*≤ = {!!}
