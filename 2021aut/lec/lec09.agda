module 2021aut.lec.lec09 where

open import lib

not : 𝟚 → 𝟚
not = λ a → if a then ff else tt

eqb : 𝟚 → 𝟚 → 𝟚
eqb = λ a b → if a then b else not b

Eqb : 𝟚 → 𝟚 → Set
Eqb = λ a b → if eqb a b then ⊤ else ⊥

Eqℕ : ℕ → ℕ → Set
Eqℕ zero zero = ⊤
Eqℕ zero (suc n) = ⊥
Eqℕ (suc m) zero = ⊥
Eqℕ (suc m) (suc n) = Eqℕ m n

canv1 : Σ ℕ (λ x → Eqℕ x (suc x) → Eqℕ (suc x) x)
canv1 = 0 , λ b → b

canv2 : Σ (ℕ → ℕ → Set) (λ R → (R zero zero ↔ R (suc zero) (suc zero)))
canv2 = (λ _ _ → ⊤) , _

R : ℕ → ℕ → Set
R zero    _ = ⊤
R (suc _) _ = ⊥

canv2' : Σ (ℕ → ℕ → Set)
  (λ R → ¬ (R zero zero ↔ R (suc zero) (suc zero)))
-- canv2' = R , λ w → π₁ w triv
canv2' = (λ m n → rec ⊤ (λ _ → ⊥) m) , λ w → π₁ w triv

canv3 : ¬ (Σ 𝟚 (λ x → ¬ Eqb x x))
canv3 = λ w →
  ind𝟚 (λ x → ¬ Eqb x x → ⊥) (λ f → f triv) (λ f → f triv) (π₁ w) (π₂ w)
--  ¬ Eqb tt tt → ⊥ = (¬ ⊤) → ⊥ = (⊤ → ⊥) → ⊥

canv4 : ¬ (Σ Set (λ A → ⊥)) -- Set × ⊥
canv4 = λ w → π₂ w

canv5 : Σ 𝟚 (λ x → ¬ Eqb x tt)
canv5 = ff , λ b → b

eqb-refl : (x : 𝟚) → Eqb x x
-- eqb-refl = ind𝟚 (λ x → Eqb x x) triv triv
eqb-refl tt = triv
eqb-refl ff = triv

notnot : (x : 𝟚) → Eqb x (not (not x))
notnot = ind𝟚 (λ x → Eqb x (not (not x))) triv triv

eqb-sym : (x y : 𝟚) → Eqb x y → Eqb y x
eqb-sym = ind𝟚 (λ x → (y : 𝟚) → Eqb x y → Eqb y x)
  (ind𝟚 (λ y → Eqb tt y → Eqb y tt) _ (λ x → x))
  (ind𝟚 (λ y → Eqb ff y → Eqb y ff) (λ x → x) _)

eqb-sym' : (x y : 𝟚) → Eqb x y → Eqb y x
eqb-sym' tt tt = _
eqb-sym' tt ff = λ x → x
eqb-sym' ff tt = λ x → x
eqb-sym' ff ff = _

transportb : (P : 𝟚 → Set){x y : 𝟚} → Eqb x y → P x → P y
transportb P {tt} {tt} _ u = u
transportb P {ff} {ff} e  u = u

eqb-sym'' : (x y : 𝟚) → Eqb x y → Eqb y x
eqb-sym'' = λ x y e →
  transportb (λ z → Eqb z x) {x}{y} e (eqb-refl x)
-- P z = Eqb z x
-- Eqb x y → P x     → P y
-- Eqb x y → Eqb x x → Eqb y x

eqb-trans : (x y z : 𝟚) → Eqb x y → Eqb y z → Eqb x z
eqb-trans x y z e e' = transportb
  (λ w → Eqb w z) {y}{x} (eqb-sym x y e) e' 
-- P w = Eqb w z
-- Eqb x y → P x     → P y
-- Eqb y x → Eqb y z → Eqb x z

eqn-refl : (n : ℕ) → Eqℕ n n
eqn-refl = indℕ (λ n → Eqℕ n n)
  triv
  (λ n ih → ih)

eqn-refl' : (n : ℕ) → Eqℕ n n
eqn-refl' zero = triv
eqn-refl' (suc n) = eqn-refl' n

nocycle : (n : ℕ) → ¬ Eqℕ n (suc n)
nocycle = indℕ (λ n → ¬ Eqℕ n (suc n))
  (λ b → b)
  (λ n ih → ih)

zero≠suc : {x : ℕ} → ¬ Eqℕ zero (suc x)
zero≠suc = λ b → b

suc-inj : {x y : ℕ} → Eqℕ (suc x) (suc y) → Eqℕ x y
suc-inj = λ e → e

_+_ : ℕ → ℕ → ℕ
-- _+_ = λ x y → rec y suc x
zero + y = y
suc n + y = suc (n + y)

-- x + z = x + z' -> z = z'
+-inj₁ : (x z z' : ℕ) → Eqℕ (x + z) (x + z') → Eqℕ z z'
+-inj₁ x z z' = indℕ (λ x → Eqℕ (x + z) (x + z') → Eqℕ z z')
  (λ e → e)
  (λ n e → e)
  x

-- ℕ +-al kommutativ monoidot (k. egysegelemes felcsoportot) alkotnak

+-assoc : (k m n : ℕ) → Eqℕ ((k + m) + n) (k + (m + n))
+-assoc k m n = indℕ (λ k → Eqℕ ((k + m) + n) (k + (m + n)))
  (eqn-refl (m + n))
  (λ n ih → ih)
  k
