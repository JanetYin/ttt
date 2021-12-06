module zh11 where
open import lib

-- Feladat: Bizonyítsd be az alább definiált Eqℕ szimmetriáját!
-- Kitöltendő lyukak a 30., 31. sorban, de akár egyből az utolsó sorban is írhatod.

pred : ℕ → ℕ ⊎ ⊤
pred = indℕ (λ _ → ℕ ⊎ ⊤) (ι₂ triv) λ n pred$n-1 → ι₁ n

predeq : (n : ℕ) → Eq (ℕ ⊎ ⊤) (pred (suc n)) (ι₁ n)
predeq n = refl

eq0 : ℕ → 𝟚
eq0 n = rec tt (λ eq0$n-1 → ff) n

eqℕ : ℕ → ℕ → 𝟚
eqℕ x y = (rec eq0 (λ eqℕ$x-1 → λ y' → case (pred y') (λ y'-1 → eqℕ$x-1 y'-1) λ y'=0 → ff) x) y

Eqℕ : ℕ → ℕ → Set
Eqℕ = λ a b → if eqℕ a b then ⊤ else ⊥

reflℕ : (a : ℕ) → Eqℕ a a
reflℕ = indℕ (λ x → Eqℕ x x) triv λ n n=n → n=n

transpℕ : (a b : ℕ) → Eqℕ a b → (P : ℕ → Set) → P a → P b
transpℕ = indℕ (λ a → (b : ℕ) → Eqℕ a b → (P : ℕ → Set) → P a → P b) (indℕ (λ b → Eqℕ zero b → (P : ℕ → Set) → P zero → P b) (λ _ _ u → u) (λ _ _ → exfalso)) (λ n ih → indℕ (λ b → Eqℕ (suc n) b → (P : ℕ → Set) → P (suc n) → P b) exfalso (λ n' ih' e P → ih n' e (λ x → P (suc x))))

-- A transpℕ függvény lesz a segítségedre
sym sym' : (a b : ℕ) → Eqℕ a b → Eqℕ b a
sym a b e = transpℕ a b e (λ x → Eqℕ x a)
  (reflℕ a) -- P a = Eqℕ a a

-- nem jó most, csak vizsgán:
sym' a b e = transpℕ b a (sym a b e) (λ x → Eqℕ b x)
  (reflℕ b)

-- Az alábbi definíciókból puskázhatsz a transpℕ használatához:

trans : (a b c : ℕ) → Eqℕ a b → Eqℕ b c → Eqℕ a c
trans a b c e e' = transpℕ b a (sym a b e) (λ x → Eqℕ x c) e'

cong : (f : ℕ → ℕ) → (a b : ℕ) → Eqℕ a b → Eqℕ (f a) (f b)
cong f a b e = transpℕ a b e (λ x → Eqℕ (f a) (f x)) (reflℕ (f a))

-- És a megoldás exportálása:

task : (a b : ℕ) → Eqℕ a b → Eqℕ b a
task = sym
