module 2021aut.t2.gy10.basic-properties where
open import lib

-- suc : ℕ → ℕ
-- suc 0 = 1
-- suc 1 = 2
-- ...
pred pred' : ℕ → ℕ ⊎ ⊤
pred = indℕ (λ _ → ℕ ⊎ ⊤) (ι₂ triv) λ n pred$n-1 → ι₁ n
pred' 1 = ι₁ 0
pred' 2 = ι₁ 1
pred' 3 = ι₁ 2
pred' (suc n) = ι₁ n
pred' 0 = ι₂ triv

predeq : (n : ℕ) → Eq (ℕ ⊎ ⊤) (pred (suc n)) (ι₁ n)
predeq n = refl -- this only works if pred is defined via indℕ and not recℕ

eq0 : ℕ → 𝟚
eq0 n = rec tt (λ eq0$n-1 → ff) n

-- use pred
eqℕ : ℕ → ℕ → 𝟚
eqℕ x y = (rec {Agda.Primitive.lzero} {(x : ℕ) → 𝟚} eq0 (λ eqℕ$x-1 → λ y' → case (pred y') (λ y'-1 → eqℕ$x-1 y'-1) λ y'=0 → ff) x) y

-- what is the difference between eqℕ a b and Eqℕ a b?
Eqℕ : ℕ → ℕ → Set
Eqℕ = λ a b → if eqℕ a b then ⊤ else ⊥

-- FONTOS
-- kisZH
-- reflexivity
-- our first proof
reflℕ : (a : ℕ) → Eqℕ a a
reflℕ = indℕ (λ x → Eqℕ x x)
  triv
  λ n n=n → n=n

-- FONTOS
-- kisZH
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

-- FONTOS
-- commutativity of equality of ℕ: use transpℕ!
sym : (a b : ℕ) → Eqℕ a b → Eqℕ b a
sym a b e = {!!}

-- FONTOS
-- transitivity of equality of ℕ: use transpℕ!
trans : (a b c : ℕ) → Eqℕ a b → Eqℕ b c → Eqℕ a c
trans a b c e e' = {!!}

-- FONTOS
-- congruence: use transpℕ!
cong cong' : (f : ℕ → ℕ) → (a b : ℕ) → Eqℕ a b → Eqℕ (f a) (f b)
cong f a b e = transpℕ a b e (λ x → Eqℕ (f a) (f x)) (reflℕ (f a))
cong' f a b e = transpℕ a b e (λ _ → Eqℕ (f a) (f b))
  {!!}

-- disjointness of different constructors of ℕ
disj : (a : ℕ) → ¬ Eqℕ zero (suc a)
disj = λ _ e → e

-- injectivity of suc
inj : (a b : ℕ) → Eqℕ a b → Eqℕ (suc a) (suc b)
inj = λ a b e → e

-- FONTOS
-- addition
_+_ : ℕ → ℕ → ℕ
_+_ = λ a b → rec b suc a
infixl 5 _+_

-- properties of addition

-- FONTOS
-- no need for indℕ
idl : (a : ℕ) → Eqℕ (0 + a) a
idl = reflℕ

-- FONTOS
-- use indℕ
-- good for practice
idr : (a : ℕ) → Eqℕ (a + 0) a
idr = {!!}

-- FONTOS
-- use indℕ
ass : (a b c : ℕ) → Eqℕ ((a + b) + c) (a + (b + c))
ass = {!λ a b c → indℕ
  (λ a → Eqℕ ((a + b) + c) (a + (b + c)))
  (reflℕ (b + c))
  (λ _ e → e)
  a!}

-- use indℕ
suc+ : (a b : ℕ) → Eqℕ (suc a + b) (a + suc b)
suc+ = {!λ a b → indℕ
  (λ a → Eqℕ (suc a + b) (a + suc b))
  (reflℕ (1 + b))
  (λ _ e → e)
  a!}
