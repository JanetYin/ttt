module 2021aut.t2.gy10.basic-properties-solved where
open import lib

pred : ℕ → ℕ ⊎ ⊤
pred = indℕ (λ _ → ℕ ⊎ ⊤) (ι₂ triv) (λ n _ → ι₁ n)
-- pred = λ n → rec       (ι₂ triv) (λ w → case w (λ n → ι₁ (suc n)) (λ _ → ι₁ zero)) n

predeq : (n : ℕ) → Eq (ℕ ⊎ ⊤) (pred (suc n)) (ι₁ n)
predeq n = refl -- this only works if pred is defined via indℕ and not recℕ

eq0 : ℕ → 𝟚
eq0 = rec tt (λ _ → ff)

eqℕ : ℕ → ℕ → 𝟚
eqℕ = rec eq0 (λ eqn m → case (pred m) eqn (λ _ → ff))

-- what is the difference between eqℕ a b and Eqℕ a b?
Eqℕ : ℕ → ℕ → Set
Eqℕ = λ a b → if eqℕ a b then ⊤ else ⊥

-- reflexivity
reflℕ : (a : ℕ) → Eqℕ a a
reflℕ = indℕ (λ x → Eqℕ x x) triv (λ n e → e)

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
