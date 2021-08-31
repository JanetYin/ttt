module tut.t1.gy08 where

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

rail : (x y z w : Bool) → Eqb x z → Eqb y w → Eqb z w → Eqb x y
rail = indBool _
               (indBool _
                        (λ _ _ _ _ _ → tt)
                        (indBool _
                                 (indBool _
                                          (λ _ → exfalso)
                                          (λ _ _ → exfalso))
                                 (λ _ → exfalso)))
               (indBool _
                        {!!}
                        {!!})

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
congb f a b e = transpb (λ x → Eqb (f a) (f x)) a b e (reflb (f a))

congb' : (f : Bool → Bool) → {a b : Bool} → Eqb a b → Eqb (f a) (f b)
congb' f {a}{b} e = congb f a b e

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
idl∧ = indBool _ tt tt

idr∧ : (a : Bool) → Eqb (a ∧ true)  a
idr∧ = indBool _ tt tt

infixl 3 _◾_ -- \sq5
_◾_ : {a b c : Bool} → Eqb a b → Eqb b c → Eqb a c
_◾_ {a}{b}{c} = transb a b c

ass∧ : (a b c : Bool) → Eqb ((a ∧ b) ∧ c) (a ∧ (b ∧ c))
ass∧ = indBool _
               (indBool _
                        (indBool _
                                 tt
                                 tt)
                        (indBool _
                                 tt
                                 tt))
               ((indBool _
                        (indBool _
                                 tt
                                 tt)
                        (indBool _
                                 tt
                                 tt)))
-- (true ∧ b) ∧ c = b ∧ c = true ∧ (b ∧ c)
-- idl : true ∧ a = a

comm∧ : (a b : Bool) → Eqb (a ∧ b) (b ∧ a)
comm∧ = indBool _
                (indBool _ tt tt)
                (indBool _ tt tt)

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
transpℕ = indℕ _
               (indℕ _ (λ _ _ e → e) λ _ _ → exfalso)
               λ n h → indℕ _ exfalso λ n' h' e P → h n' e (λ x → P (suc x))

-- commutativity of equality of ℕ: use transpℕ!
sym : (a b : ℕ) → Eqℕ a b → Eqℕ b a
sym a b e = transpℕ a b e (λ n → Eqℕ n a) (reflℕ a)

-- transitivity of equality of ℕ: use transpℕ!
trans : (a b c : ℕ) → Eqℕ a b → Eqℕ b c → Eqℕ a c
trans a b c e e' = transpℕ b c e' (λ n → Eqℕ a n) e

-- congruence: use transpℕ!
cong : (f : ℕ → ℕ) → (a b : ℕ) → Eqℕ a b → Eqℕ (f a) (f b)
cong f a b e = transpℕ a b e (λ n → Eqℕ (f a) (f n)) (reflℕ (f a))

-- disjointness of different constructors of ℕ
disj : (a : ℕ) → ¬ Eqℕ zero (suc a)
disj = λ a → exfalso

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
idr = indℕ _ tt λ _ e → e

-- use indℕ
ass : (a b c : ℕ) → Eqℕ ((a + b) + c) (a + (b + c))
ass = indℕ _
           (λ b c → trans (zero + b + c) (b + c) (zero + (b + c))
                          (cong (λ x → x + c) (zero + b) b (idl b))
                          (idl (b + c)))
           λ n h → h

-- (suc n + b) + c = suc (n + b) + c = suc ((n + b) + c)
-- suc n + (b + c) = suc (n + (b + c))
-- kell: Eq (suc ((n + b) + c)) (suc (n + (b + c))) = Eq (n + (b + c)) (n + (b + c))

-- use indℕ
suc+ : (a b : ℕ) → Eqℕ (suc a + b) (a + suc b)
suc+ = λ a b → indℕ (λ a → Eqℕ (suc a + b) (a + suc b))
                    (reflℕ (suc b))
                    (λ _ h → h)
                    a
-- suc 0 + b = suc (0 + b) = suc b  

-- use indℕ, trans, suc+
comm : (a b : ℕ) → Eqℕ (a + b) (b + a)
comm = λ a b → indℕ (λ a → Eqℕ (a + b) (b + a))
                    (sym (b + zero) b (idr b))  -- Eqℕ b (b + zero)
                    (λ n h → trans (suc n + b) (suc b + n) (b + suc n)
                                   h
                                   (suc+ b n))             
                    a

_*_ : ℕ → ℕ → ℕ
_*_ = λ a b → rec 0 (_+_ b) a
infixl 7 _*_

todo : (n m : ℕ) → Eqℕ (n + m + n) (m + n + n)
todo = λ n m → cong (λ c → c + n) (n + m) (m + n) (comm n m)

-- laws for muliplication

-- use indℕ
idl* : (a : ℕ) → Eqℕ (1 * a) a
idl* = indℕ (λ a → Eqℕ (1 * a) a)
            tt
            λ n h → h
-- rec 0 (_+_ 0) (suc zero) = zero


-- use indℕ
idr* : (a : ℕ) → Eqℕ (a * 1) a
idr* = indℕ _ tt λ n h → h
-- suc n * 1 = rec 0 (1 +_ ) (suc n) = 1 + rec 0 (_+_ 1) n
-- rec u v (suc n) = v (rec u v n)

-- no need for indℕ
nulll : (a : ℕ) → Eqℕ (0 * a) 0
nulll = λ a → tt
-- λ a b → rec 0 (_+_ b) a

-- use indℕ
nullr : (a : ℕ) → Eqℕ (a * 0) 0
nullr = indℕ _ tt λ n h → h

-- use indℕ, trans, cong, sym, ass
distr : (a b c : ℕ) → Eqℕ ((a + b) * c) (a * c + b * c)
distr = λ a b c → indℕ
          (λ a → Eqℕ ((a + b) * c) (a * c + b * c))
          (reflℕ (b * c))
          (λ n h → trans
            ((suc n + b) * c)
            (c + (n * c + b * c))
            (suc n * c + b * c)
            (cong (λ x → c + x) ((n + b) * c) (n * c + b * c) h)
            (sym (suc n * c + b * c) (c + (n * c + b * c))
                 (ass c (n * c) (b * c))))
          a
-- (zero + b) * c = b * c
-- zero * c + b * c = zero + b * c = b * c
-- (suc n + b) * c = suc (n + b) * c = c + (n + b) * c
-- suc n * c + b * c = (c + n * c) + b * c
-- c + (n + b) * c            =Eqℕ= cong, ind. hip 
-- c + (n * c + b * c)        =Eqℕ= ass+, sym
-- (c + n * c) + b * c 

-- use indℕ, trans, distr, cong
ass* : (a b c : ℕ) → Eqℕ ((a * b) * c) (a * (b * c))
ass* = λ a b c → indℕ
         (λ a → Eqℕ ((a * b) * c) (a * (b * c)))
         (reflℕ 0)
         (λ n h → trans
           (suc n * b * c)
           (b * c + n * b * c)
           (suc n * (b * c))
           (distr b (n * b) c)
           (cong (λ x → b * c + x) (n * b * c) (n * (b * c)) h))
         a
-- (zero * b) * c = zero * c = zero
-- zero * (b * c) = zero
-- (suc n * b) * c = (b + n * b) * c
-- suc n * (b * c) = b * c + (n * (b * c))

-- (b + n * b) * c            =Eqℕ= distr
-- b * c + n * b * c          =Eqℕ= cong, ind. hip
-- b * c + n * (b * c)

-- use indℕ, trans, sym, ass, cong, comm
suc* : (a b : ℕ) → Eqℕ (a + a * b) (a * suc b)
suc* = {!!}

-- use indℕ, nullr, trans, suc*
comm* : (a b : ℕ) → Eqℕ (a * b) (b * a)
comm* = {!!}

-- left distributivity: use comm* and distr
distl : (a b c : ℕ) → Eqℕ (a * (b + c)) (a * b + a * c)
distl = {!!}
