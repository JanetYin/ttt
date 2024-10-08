module tut.t3.gy08 where

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
reflb = indBool _ tt tt

transpb : (P : Bool → Set)(a b : Bool) → Eqb a b → P a → P b
transpb = λ P a → indBool 
  (λ a → (b : Bool) → Eqb a b → P a → P b)
  (λ b → indBool (λ b → Eqb true  b → P true  → P b) (λ _ w → w) exfalso     b)
  (λ b → indBool (λ b → Eqb false b → P false → P b) exfalso     (λ _ w → w) b)
  a

-- use transpb
symb : (a b : Bool) → Eqb a b → Eqb b a
symb a b e = transpb (λ b → Eqb b a) a b e (reflb a)

-- use transpb
transb : (a b c : Bool) → Eqb a b → Eqb b c → Eqb a c
transb a b c u v = transpb (λ c → Eqb a c) b c v u

-- every function on booleans is a congruence; use transpb to prove it
congb : (f : Bool → Bool) → (a b : Bool) → Eqb a b → Eqb (f a) (f b)
congb = λ f a b eq → transpb (λ x → Eqb (f a) (f x)) a b eq (reflb (f a))

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
idl∧ = indBool (λ b → Eqb (true ∧ b) b) tt tt

idr∧ : (a : Bool) → Eqb (a ∧ true)  a
idr∧ = indBool (λ b → Eqb (b ∧ true) b) tt tt

ass∧ : (a b c : Bool) → Eqb ((a ∧ b) ∧ c) (a ∧ (b ∧ c))
ass∧ = λ a b c → indBool (λ a → Eqb ((a ∧ b) ∧ c) (a ∧ (b ∧ c)))
                         (reflb (b ∧ c))
                         (reflb false)
                         a

comm∧ : (a b : Bool) → Eqb (a ∧ b) (b ∧ a)
comm∧ = λ a b → indBool (λ a → Eqb (a ∧ b) (b ∧ a))
                        (transb (true ∧ b) b (b ∧ true) (idl∧ b) (symb (b ∧ true) b (idr∧ b)))
                        ((transb (false ∧ b) false (b ∧ false) (reflb false) (indBool (λ b → Eqb false (b ∧ false)) tt tt b)))
                        a

null∧ : (a : Bool) → Eqb (false ∧ a) false
null∧ = λ _ → reflb false

idl∨ : (a : Bool) → Eqb (false ∨ a) a
idl∨ = reflb

idr∨ : (a : Bool) → Eqb (a ∨ false) a
idr∨ = indBool (λ a → Eqb (a ∨ false) a) tt tt

ass∨ : (a b c : Bool) → Eqb ((a ∨ b) ∨ c) (a ∨ (b ∨ c))
ass∨ = λ a b c → indBool (λ a → Eqb ((a ∨ b) ∨ c) (a ∨ (b ∨ c)))
                         (reflb true)
                         (reflb (b ∨ c))
                         a

comm∨ : (a b : Bool) → Eqb (a ∨ b) (b ∨ a)
comm∨ = indBool (λ a → (b : Bool) → Eqb (a ∨ b) (b ∨ a))
                          (indBool (λ b → Eqb (true ∨ b) (b ∨ true)) tt tt)
                          (indBool (λ b → Eqb (false ∨ b) (b ∨ false)) tt tt)

null∨ : (a : Bool) → Eqb (true ∨ a) true
null∨ = λ _ → reflb true

dist∧ : (a b c : Bool) → Eqb (a ∧ (b ∨ c)) (a ∧ b ∨ a ∧ c)
dist∧ = indBool (λ a → (b c : Bool) → Eqb (a ∧ (b ∨ c)) (a ∧ b ∨ a ∧ c))
                          (indBool (λ b → (c : Bool) → Eqb (true ∧ (b ∨ c)) (true ∧ b ∨ true ∧ c)) 
                                   (indBool (λ c → Eqb (true ∧ (true ∨ c)) (true ∧ true ∨ true ∧ c)) tt tt)
                                   (indBool (λ c → Eqb (true ∧ (false ∨ c)) (true ∧ false ∨ true ∧ c)) tt tt)
                          )
                          (indBool (λ b → (c : Bool) → Eqb (false ∧ (b ∨ c)) (false ∧ b ∨ false ∧ c)) 
                                   (indBool (λ c → Eqb (false ∧ (true ∨ c)) (false ∧ true ∨ false ∧ c)) tt tt)
                                   (indBool (λ c → Eqb (false ∧ (false ∨ c)) (false ∧ false ∨ false ∧ c)) tt tt)
                          )

dist∨ : (a b c : Bool) → Eqb (a ∨ (b ∧ c)) ((a ∨ b) ∧ (a ∨ c))
dist∨ = indBool (λ a → (b c : Bool) → Eqb (a ∨ (b ∧ c)) ((a ∨ b) ∧ (a ∨ c)))
                          (indBool (λ b → (c : Bool) → Eqb (true ∨ (b ∧ c)) ((true ∨ b) ∧ (true ∨ c))) 
                                   (indBool (λ c → Eqb (true ∨ (true ∧ c)) ((true ∨ true) ∧ (true ∨ c))) tt tt)
                                   (indBool (λ c → Eqb (true ∨ (false ∧ c)) ((true ∨ false) ∧ (true ∨ c))) tt tt)
                          )
                          (indBool (λ b → (c : Bool) → Eqb (false ∨ (b ∧ c)) ((false ∨ b) ∧ (false ∨ c))) 
                                   (indBool (λ c → Eqb (false ∨ (true ∧ c)) ((false ∨ true) ∧ (false ∨ c))) tt tt)
                                   (indBool (λ c → Eqb (false ∨ (false ∧ c)) ((false ∨ false) ∧ (false ∨ c))) tt tt)
                          )

abs∧ : (a b : Bool) → Eqb (a ∧ (a ∨ b)) a
abs∧ = λ a b → indBool (λ a → Eqb (a ∧ (a ∨ b)) a) tt tt a

abs∨ : (a b : Bool) → Eqb (a ∨ (a ∧ b)) a
abs∨ = λ a b → indBool (λ a → Eqb (a ∨ (a ∧ b)) a) tt tt a

deMorgan' : (a b : Bool) → Eqb (not (a ∨ b)) (not a ∧ not b)
deMorgan' = indBool (λ a → (b : Bool) → Eqb (not (a ∨ b)) (not a ∧ not b))
                     (λ b → indBool
                             (λ b → Eqb (not (true ∨ b)) (not true ∧ not b))
                             tt
                             tt
                             b
                     )
                     λ b → transpb (λ x → Eqb (not x) (true ∧ not b)) b (false ∨ b)
                            (symb (false ∨ b) b (idl∨ b))
                            (symb (true ∧ not b) (not b) (idl∧ (not b)))

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
reflℕ = indℕ (λ x → Eqℕ x x) tt λ n e → e

-- transport
transpℕ : (a b : ℕ) → Eqℕ a b → (P : ℕ → Set) → P a → P b
transpℕ = indℕ (λ a → (b : ℕ) → Eqℕ a b → (P : ℕ → Set) → P a → P b)
                (indℕ (λ b → Eqℕ zero b → (P : ℕ → Set) → P zero → P b)
                      (λ _ _ p0 → p0)
                      λ _ _ e _ _ → exfalso e)
                λ n ih → indℕ (λ b → Eqℕ (suc n) b → (P : ℕ → Set) → P (suc n) → P b)
                               exfalso
                               λ n' ih' e P Psucn → ih n' e (λ x → P (suc x)) Psucn

-- commutativity of equality of ℕ: use transpℕ!
sym : (a b : ℕ) → Eqℕ a b → Eqℕ b a
sym a b e = {!!}

-- transitivity of equality of ℕ: use transpℕ!
trans : (a b c : ℕ) → Eqℕ a b → Eqℕ b c → Eqℕ a c
trans a b c e e' = {!!}

-- congruence: use transpℕ!
cong : (f : ℕ → ℕ) → (a b : ℕ) → Eqℕ a b → Eqℕ (f a) (f b)
cong f a b e = {!!}

-- disjointness of different constructors of ℕ
disj : (a : ℕ) → ¬ Eqℕ zero (suc a)
disj = {!!}

-- injectivity of suc
inj : (a b : ℕ) → Eqℕ a b → Eqℕ (suc a) (suc b)
inj = {!!}

-- addition
_+_ : ℕ → ℕ → ℕ
_+_ = λ a b → rec b suc a
infixl 5 _+_

-- properties of addition

-- no need for indℕ
idl : (a : ℕ) → Eqℕ (0 + a) a
idl = {!!}

-- use indℕ
idr : (a : ℕ) → Eqℕ (a + 0) a
idr = {!!}

-- use indℕ
ass : (a b c : ℕ) → Eqℕ ((a + b) + c) (a + (b + c))
ass = {!!}

-- use indℕ
suc+ : (a b : ℕ) → Eqℕ (suc a + b) (a + suc b)
suc+ = {!!}

-- use indℕ, trans, suc+
comm : (a b : ℕ) → Eqℕ (a + b) (b + a)
comm = {!!}

_*_ : ℕ → ℕ → ℕ
_*_ = λ a b → rec 0 (_+_ b) a
infixl 7 _*_

-- laws for muliplication

-- use indℕ
idl* : (a : ℕ) → Eqℕ (1 * a) a
idl* = {!!}

-- use indℕ
idr* : (a : ℕ) → Eqℕ (a * 1) a
idr* = {!!}

-- no need for indℕ
nulll : (a : ℕ) → Eqℕ (0 * a) 0
nulll = {!!}

-- use indℕ
nullr : (a : ℕ) → Eqℕ (a * 0) 0
nullr = {!!}

-- trans egy kényelmesebb változata \sq5
_◾_ : {a b c : ℕ} → Eqℕ a b → Eqℕ b c → Eqℕ a c
_◾_ {a}{b}{c} = trans a b c

-- use indℕ, trans, cong, sym, ass
distr : (a b c : ℕ) → Eqℕ ((a + b) * c) (a * c + b * c)
distr = {!!}

-- use indℕ, trans, distr, cong
ass* : (a b c : ℕ) → Eqℕ ((a * b) * c) (a * (b * c))
ass* = {!!}

-- use indℕ, trans, sym, ass, cong, comm
suc* : (a b : ℕ) → Eqℕ (a + a * b) (a * suc b)
suc* = {!!}

{-
Biz be teljes indukcioval:
a = 0 esetre:
  0 * b = b * 0      (nulll/def)
  0     = b * 0      (nullr)
  0     = 0
a = n + 1 eseten tfh h ih: n * b = b * n
  (n + 1) * b = b * (n + 1) mivel
  (n + 1) * b =      (def)
  b + n * b   =      (cong, ih)
  b + b * n   =      (suc*)
  b * (1 + n)
-}

-- use indℕ, nullr, trans, suc*
comm* : (a b : ℕ) → Eqℕ (a * b) (b * a)
comm* = λ a b → indℕ
  (λ a → Eqℕ (a * b) (b * a))
  (sym (b * zero) (zero * b) (nullr b))
  (λ n ih → trans
    (b + n * b)
    (b + b * n)
    (b * (1 + n))
    (cong (λ w → b + w) (n * b) (b * n) ih)
    (suc* b n))
  a

{-
a * (b + c) = (comm)
(b + c) * a = (distr)
b * a + c * a = (comm)
a * b + c * a = (comm)
a * b + a * c
-}

-- left distributivity: use comm* and distr
distl : (a b c : ℕ) → Eqℕ (a * (b + c)) (a * b + a * c)
distl = λ a b c → trans
  (a * (b + c))
  ((b + c) * a)
  (a * b + a * c)
  (comm* a (b + c))
  (trans
    ((b + c) * a)
    (b * a + c * a)
    (a * b + a * c)
    (distr b c a)
    (trans
      (b * a + c * a)
      (a * b + c * a)
      (a * b + a * c)
      (cong (λ x → x + c * a) (b * a) (a * b) (comm* b a))
      (cong (λ x → a * b + x) (c * a) (a * c) (comm* c a))))


  

-------------------------------------------------
-- building on the above
-------------------------------------------------

{-
x + x     =   (idl*)
x + 1 * x =   (def)
2 * x
-}

x+x : (x : ℕ) → Eqℕ (x + x) (2 * x)
x+x = {!!}

ass-comm : (x y z : ℕ) → Eqℕ (x + y + z) (x + z + y)
ass-comm = {!!}

{-
x + (y + 0) + x = 2 * x + y
x + (y + 0) + x = (idr) 
x + y + x       = (ass-comm)
x + x + y       = (x+x)
2 * x + y
-}

p4 : (x y : ℕ) → Eqℕ ((x + (y + zero)) + x) (2 * x + y)
p4 = λ x y → trans
  ((x + (y + zero)) + x)
  (x + y + x)
  (2 * x + y)
  (cong (λ w → x + w + x) (y + zero) y (idr y))
  (trans
    (x + y + x)
    (x + x + y)
    (2 * x + y)
    (ass-comm x y x)
    (cong (λ w → w + y) (x + x) (2 * x) (x+x x) ))


p3 : (a b : ℕ) → Eqℕ (a + a + b + a * 0) (2 * a + b)
p3 = {!!}

p2 : (a b c : ℕ) → Eqℕ (c * (b + 1 + a)) (a * c + b * c + c)
p2 = {!!}

_^_ : ℕ → ℕ → ℕ
a ^ n = rec 1 (_* a) n
infixl 9 _^_

a*a : (a : ℕ) → Eqℕ (a * a) (a ^ 2)
a*a = {!!}

{-
(a + b) ^ 2 =   (def)
(a + b) * (a + b) ^ 1 = (^1)
(a + b) * (a + b)  = (distl)
(a + b) * a + (a + b) * b = (distr)
a * a + b * a + (a + b) * b = (distr)
a * a + b * a + (a * b + b * b) = (a*a)
a ^ 2 +	b * a + (a * b + b * b) = (a*a)
a ^ 2 + b * a + (a * b + b ^ 2) = (ass)
a ^ 2 + b * a + a * b + b ^ 2 = (comm)
a ^ 2 + a * b + a * b + b ^ 2  = (a+a)
a ^ 2 + 2 * a * b + b ^ 2
-}

p1 : (a b : ℕ) → Eqℕ ((a + b) ^ 2) (a ^ 2 + 2 * a * b + b ^ 2)
p1 = {!!}

-------------------------------------------------
-- laws about exponentiation
-------------------------------------------------

0^ : (n : ℕ) → Eqℕ (0 ^ suc n) 0
0^ = {!!}

^0 : (a : ℕ) → Eqℕ (a ^ 0) 1
^0 = {!!}

1^ : (n : ℕ) → Eqℕ (1 ^ n) 1
1^ = {!!}

^1 : (a : ℕ) → Eqℕ (a ^ 1) a
^1 = {!!}

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
refl≤ (suc x) = refl≤ x

trans≤ : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
trans≤ zero    y       z       e e' = tt
trans≤ (suc x) (suc y) (suc z) e e' = trans≤ x y z e e'

≤dec : (x y : ℕ) → x ≤ y ⊎ y ≤ x
≤dec zero y = inj₁ tt
≤dec (suc x) zero = inj₂ tt
≤dec (suc x) (suc y) = ≤dec x y

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


---------------------------------------------------------
-- First order logic
---------------------------------------------------------

∀×-distr  : (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
∀×-distr = {!!}

∀⊎-distr  : (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a ⊎ Q a)  ← ((a : A) → P a) ⊎ ((a : A) → Q a)
∀⊎-distr = {!!}

∀⊎-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (((a : A) → P a ⊎ Q a) → ((a : A) → P a) ⊎ ((a : A) → Q a)))
∀⊎-distr' = λ f → case (f ℕ isEven isOdd everyℕisEvenOrOdd) (λ allEven → allEven 1) λ allOdd → allOdd 0
  where
    isEven : ℕ → Set
    isEven = {!!}
    isOdd : ℕ → Set
    isOdd = {!!}
    everyℕisEvenOrOdd : (n : ℕ) → isEven n ⊎ isOdd n
    everyℕisEvenOrOdd = {!!}

Σ×-distr  : (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a × Q a)  → Σ A P × Σ A Q
Σ×-distr = {!!}

Σ×-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → ((Σ A λ a → P a × Q a) ← Σ A P × Σ A Q))
Σ×-distr' = {!!}

Σ⊎-distr : (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a)  ↔ Σ A P ⊎ Σ A Q
Σ⊎-distr = {!!}

¬∀ : (A : Set)(P : A → Set) → (Σ A λ a → ¬ P a) → ¬ ((a : A) → P a)
¬∀ = {!!}

¬Σ : (A : Set)(P : A → Set) → (¬ Σ A λ a → P a) ↔ ((a : A) → ¬ P a)
¬Σ = {!!}

⊎↔ΣBool : (A B : Set) → (A ⊎ B) ↔ Σ Bool (λ b → if b then A else B)
⊎↔ΣBool = {!!}

¬¬∀-nat : (A : Set)(P : A → Set)  → ¬ ¬ ((x : A) → P x) → (x : A) → ¬ ¬ (P x)
¬¬∀-nat = {!!}

Σ∀ : (A B : Set)(R : A → B → Set) → (Σ A λ x → (y : B) → R x y) → (y : B) → Σ A λ x → R x y
Σ∀ = {!!}

AC : (A B : Set)(R : A → B → Set) → ((x : A) → Σ B λ y → R x y) → Σ (A → B) λ f → (x : A) → R x (f x)
AC = {!!}
