module zh09 where
open import lib

Eq𝟚 : 𝟚 → 𝟚 → Set
Eq𝟚 tt tt = ⊤
Eq𝟚 ff ff = ⊤
Eq𝟚 tt ff = ⊥
Eq𝟚 ff tt = ⊥

task₁ task₂ : {f : 𝟚 → 𝟚}{x : 𝟚} → Eq𝟚 (f x) x → Eq𝟚 (f x) (f x) → Eq𝟚 (f x) tt ⊎ Eq𝟚 (f x) ff
{-
task {f} {x} eq₁ eq₂ = ind𝟚 (λ f$x → Eq𝟚 (f x) f$x → Eq𝟚 (f x) tt ⊎ Eq𝟚 (f x) ff)
  ι₁
  ι₂
  (f x) (ind𝟚 (λ f$x → Eq𝟚 f$x f$x) triv triv (f x))
-}
-- Do not use `triv`
task₁ {f} {x} eq₁ _ = ind𝟚 (λ b → Eq𝟚 (f b) b → Eq𝟚 (f b) tt ⊎ Eq𝟚 (f b) ff)
                               -- Eq𝟚 (f x) tt ⊎ Eq𝟚 (f x) ff
-- eq₁ : Eq𝟚 (f tt) tt
  (λ eq₁' → ι₁ eq₁')
  (λ eq₁' → ι₂ eq₁')
  x eq₁
task₂ {f} {x} _ eq₂ = ind𝟚 (λ b → Eq𝟚 b b → Eq𝟚 ( b ) tt ⊎ Eq𝟚 ( b ) ff)
  -- Eq𝟚 (f x) tt ⊎ Eq𝟚 (f x) ff
  -- Eq𝟚 ( b ) tt ⊎ Eq𝟚 ( b ) ff
  (λ triv' → ι₁ triv') -- Eq𝟚 tt tt → Eq𝟚 ( tt ) tt ⊎ Eq𝟚 ( tt ) ff
  (λ triv' → ι₂ triv') -- Eq𝟚 ff ff → Eq𝟚 ( ff ) tt ⊎ Eq𝟚 ( ff ) ff
  (f x) eq₂
