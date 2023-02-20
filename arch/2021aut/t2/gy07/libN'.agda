module 2021aut.t2.gy07.libN' where
open import lib

_=0 : ℕ → 𝟚
n =0 = rec tt (λ n-1=0 → ff) n

pred : ℕ → ⊤ ⊎ ℕ
pred n = let
  t = rec (ι₁ triv) (λ x → case x (λ ι₁triv → ι₂ zero) (λ n → ι₂ n)) n
  in t

eq : ℕ → ℕ → 𝟚
eq x = indℕ {!!} {!!} {!!} x
 --rec (λ y → y =0) (λ =x-1 → λ y → (case (pred y) (λ _ → ff) λ y-1 → =x-1 y-1)) x

Eqℕ : ℕ → ℕ → Set
Eqℕ x y = if eq x y then ⊤ else ⊥

reflℕ : (a : ℕ) → Eqℕ a a
reflℕ a = indℕ (λ a → Eqℕ a a) triv (λ n n-1=n-1 → {!!}) a
