module tut.t2.gy08 where

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
congb = {!!}

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
transpℕ = {!!}

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

-- use indℕ, nullr, trans, suc*
comm* : (a b : ℕ) → Eqℕ (a * b) (b * a)
comm* = {!!}

-- left distributivity: use comm* and distr
distl : (a b c : ℕ) → Eqℕ (a * (b + c)) (a * b + a * c)
distl = {!!}
