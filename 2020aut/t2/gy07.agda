module tut.t2.gy07 where

open import lib

-------------------------------------------------
-- Bool
-------------------------------------------------

not : Bool → Bool
not = λ a → if a then false else true

eqb : Bool → Bool → Bool
eqb = λ a b → if a then b else not b

Eqb : Bool → Bool → Set
Eqb true  true  = ⊤
Eqb false false = ⊤
Eqb _     _     = ⊥

-- what is the difference of eqb and Eqb?

-- unit tests

nonottrue : Eqb (not (not true)) true
nonottrue = tt

noteq : ¬ Eqb false true
noteq = λ b → b

lem0 : Eqb true false → Eqb false true
lem0 = λ e → e

-- dependent elimination of Bool
refl-Eqb : (b : Bool) → Eqb b b
refl-Eqb = λ b → indBool (λ x → Eqb x x) tt tt b

lem1 : (x : Bool) → Eqb true x → ¬ Eqb x false
lem1 = λ x → indBool (λ b → Eqb true b → ¬ Eqb b false) (λ _ b → b) (λ b _ → b) x 

notnot : (x : Bool) → Eqb (not (not x)) x
notnot = λ x → indBool (λ b → Eqb (not (not b)) b) tt tt x

sym-Eqb : (a b : Bool) → Eqb a b → Eqb b a
sym-Eqb = λ a b → indBool (λ x → Eqb a x → Eqb x a)
                  (indBool (λ x → Eqb x true → Eqb true x) (λ tt → tt) (λ b → b) a)
                  (indBool (λ x → Eqb x false → Eqb false x) (λ b → b) (λ tt → tt) a)
                  b

transp-Eqb : (P : Bool → Set)(a b : Bool) → Eqb a b → P a → P b
transp-Eqb = λ P a b → indBool (λ x → Eqb a x → P a → P x)
                        (indBool (λ x → Eqb x true → P x → P true) (λ _ pt → pt) (λ b _ → exfalso b) a)
                        {!!}
                        b

-- solve this using transp-Eqb! (without using indBool)
trans-Eqb : (a b c : Bool) → Eqb a b → Eqb b c → Eqb a c
trans-Eqb = {!!}

notBoolFunction : ¬ ((f : Bool → Bool) → (x : Bool) → Eqb (f (f x)) x)
notBoolFunction = {!!}

-- hard:
boolFunction : (f : Bool → Bool)(x : Bool) → Eqb (f (f (f x))) (f x)
boolFunction = {!!}

-------------------------------------------------
-- Natural numbers
-------------------------------------------------

{-
    n                                    pred n
    ----------------------------------------------------------------------------------------
    0 = zero                             inj₂ tt
    1 = suc zero                         inj₁ zero
    2 = suc (suc zero)                   inj₁ (suc zero)
    3 = suc (suc (suc zero))             inj₁ (suc (suc zero))
    4 = suc (suc (suc (suc zero)))       inj₁ (suc (suc (suc zero)))
    ...                                  ...
-}
pred : ℕ → ℕ ⊎ ⊤
pred = rec (inj₂ tt) (λ w → case w (λ n → inj₁ (suc n)) (λ _ → inj₁ zero))

pred' : ℕ → ℕ ⊎ ⊤
pred' = λ x → indℕ (λ _ → ℕ ⊎ ⊤) (inj₂ tt) (λ n _ → inj₁ n) x
--indℕ : (P : ℕ → Set) → P zero → ((n : ℕ) → P n → P (suc n)) → (t : ℕ) → P t


-- What's the difference between pred and pred'?

-- For every number n = suc (suc ... (suc zero)) (n number of sucs),
-- we have that pred (suc n) = inj₁ n and pred' (suc n) = inj₁ n. We
-- don't have that for every variable n, pred (suc n) = inj₁ n, but we
-- do have that for every variable n, pred' (suc n) = inj₁ n. This is
-- why pred' is nicer than pred.

{-
    x                                    eq0 x
    -----------------------------------------------------------------------------------------------
    0 = zero                             true
    1 = suc zero                         (λ _ → false) true = false
    2 = suc (suc zero)                   (λ _ → false) ((λ _ → false) true) = false
    3 = suc (suc (suc zero))             (λ _ → false) ((λ _ → false) ((λ _ → false) true)) = false
    ...                                  ...
-}
eq0 : ℕ → Bool
eq0 = rec true (λ _ → false)

{-
    n                                    eq n
    ----------------------------------------------------------------------------------------
    0 = zero                             eq0
    1 = suc zero                         "eq0 ∘ pred"
    2 = suc (suc zero)                   "eq1 ∘ pred"
    3 = suc (suc (suc zero))             "eq2 ∘ pred"
    4 = suc (suc (suc (suc zero)))       "eq3 ∘ pred"
    ...                                  ...

Because `pred` returns a `ℕ ⊎ ⊤`, we have to handle the `inj₂ tt` case:

    n                                    eq n
    ----------------------------------------------------------------------------------------
    0 = zero                             eq0
    1 = suc zero                         λ m → case (pred m) eq0 (λ _ → false)
    2 = suc (suc zero)                   λ m → case (pred m) eq1 (λ _ → false)
    3 = suc (suc (suc zero))             λ m → case (pred m) eq2 (λ _ → false)
    4 = suc (suc (suc (suc zero)))       λ m → case (pred m) eq3 (λ _ → false)
    ...                                  ...
-}
eqℕ : ℕ → ℕ → Bool
eqℕ = rec eq0 (λ eqn-1 n → case (pred' n) eqn-1 λ _ → false)

-- what is the difference between eqℕ a b and Eqℕ a b?
Eqℕ : ℕ → ℕ → Set
Eqℕ = λ a b → if eqℕ a b then ⊤ else ⊥ 

-- unit tests:

10=10 : Eqℕ 10 10
10=10 = tt

10≠7 : ¬ Eqℕ 10 7
10≠7 = λ b → b

7≠10 : ¬ Eqℕ 7 10
7≠10 = λ b → b

-- properties of equality (no need for induction)

lem4 : ¬ Eqℕ zero zero → Eqℕ zero (suc zero)
lem4 = λ e → e tt

eqzerozero : Eqℕ zero zero
eqzerozero = tt

eqsuczero : (a : ℕ) → ¬ Eqℕ (suc a) zero
eqsuczero = λ _ b → b

eqzerosuc : (a : ℕ) → ¬ Eqℕ zero (suc a)
eqzerosuc = λ _ b → b

lem5 : ¬ Eqℕ zero zero → Eqℕ zero (suc zero)
lem5 = λ e → e tt

-- this only needs induction if pred is used in eqℕ and not pred'
eqsucsuc : (a b : ℕ) → Eqℕ (suc a) (suc b) → Eqℕ a b
eqsucsuc = {!!}

-- induction on ℕ

Eqℕ-refl : (x : ℕ) → Eqℕ x x
Eqℕ-refl = λ x → indℕ (λ n → Eqℕ n n) tt (λ n eqn → eqn) x

_+_ : ℕ → ℕ → ℕ
_+_ = λ a b → rec b suc a

+-assoc : (x y z : ℕ) → Eqℕ ((x + y) + z) (x + (y + z))
+-assoc = {!!}

+-idl : (x : ℕ) → Eqℕ (zero + x) x
+-idl = {!!}

+-idr : (x : ℕ) → Eqℕ x (x + zero)
+-idr = {!!}

-- difficult
Eqℕ-sym : (a b : ℕ) → Eqℕ a b → Eqℕ b a
Eqℕ-sym = {!!}

-- use Eqℕ-sym!
lem3 : (x : ℕ) → Eqℕ x (suc (suc zero)) → Eqℕ (suc (suc (suc zero))) (suc x)
lem3 = {!!}
