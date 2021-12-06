module 2021aut.t2.zh.zh10 where
open import lib

Eq𝟚 : 𝟚 → 𝟚 → Set
Eq𝟚 tt tt = ⊤
Eq𝟚 ff ff = ⊤
Eq𝟚 tt ff = ⊥
Eq𝟚 ff tt = ⊥

_∨_ : 𝟚 → 𝟚 → 𝟚 -- \or
_∨_ = λ x y → if x then tt else y
infixl 5 _∨_

{-
x ∈ 𝟚
x ∈ { tt ; ff }
x = tt -> Eq𝟚 tt ∨ ff
x = ff -> Eq𝟚 ff ∨ ff
-}
idr∨ : (x : 𝟚) → Eq𝟚 (x ∨ ff) x
idr∨ x = ind𝟚 (λ x → Eq𝟚 (x ∨ ff) x)
  triv
  triv
  x

idl∨ : (x : 𝟚) → Eq𝟚 (ff ∨ x) x
idl∨ x = ind𝟚 (λ x → Eq𝟚 (ff ∨ x) x)
  triv
  triv
  x

trans𝟚 : {x y z : 𝟚} → Eq𝟚 x y → Eq𝟚 y z → Eq𝟚 x z
trans𝟚 {x} {y} {z} = λ eq₁ eq₂ → ind𝟚 (λ x → Eq𝟚 x y → Eq𝟚 y z → Eq𝟚 x z)
  (λ eq₁ eq₂ → ind𝟚 (λ z → Eq𝟚 tt y → Eq𝟚 y z → Eq𝟚 tt z)
    (λ _ _ → triv)
    (λ eq₁ eq₂ → ind𝟚 (λ y → Eq𝟚 tt y → Eq𝟚 y ff → Eq𝟚 tt ff) (λ _ eq₂ → eq₂) (λ eq₁ _ → eq₁) y eq₁ eq₂)
    z eq₁ eq₂)
  (λ eq₁ eq₂ → ind𝟚 (λ z → Eq𝟚 ff y → Eq𝟚 y z → Eq𝟚 ff z)
    (λ eq₁ eq₂ → ind𝟚 (λ y → Eq𝟚 ff y → Eq𝟚 y tt → Eq𝟚 tt ff) (λ eq₁ _ → eq₁) (λ _ eq₂ → eq₂) y eq₁ eq₂)
    (λ _ _ → triv)
    z eq₁ eq₂)
  x eq₁ eq₂

sym𝟚 : {x y : 𝟚} → Eq𝟚 x y → Eq𝟚 y x
sym𝟚 {x} {y} = λ eq → ind𝟚 (λ x → Eq𝟚 x y → Eq𝟚 y x)
  (λ eq → ind𝟚 (λ y → Eq𝟚 tt y → Eq𝟚 y tt)
    (λ _ → triv)
    (λ eq → eq)
    y eq)
  (λ eq → ind𝟚 (λ y → Eq𝟚 ff y → Eq𝟚 y ff)
    (λ eq → eq)
    (λ _ → triv)
    y eq)
  x eq

transp𝟚 : {x y : 𝟚}{P : 𝟚 → Set} → Eq𝟚 x y → P x → P y
transp𝟚 {x} {y} {P} = λ eq px → ind𝟚 (λ x → Eq𝟚 x y → P x → P y)
  (λ eq p$tt → ind𝟚 (λ y → Eq𝟚 tt y → P tt → P y) (λ _ p$tt → p$tt) (λ bot _ → exfalso bot) y eq p$tt)
  (λ eq p$ff → ind𝟚 (λ y → Eq𝟚 ff y → P ff → P y) (λ bot _ → exfalso bot) (λ _ p$ff → p$ff) y eq p$ff)
  x eq px

refl𝟚 : {x : 𝟚} → Eq𝟚 x x
refl𝟚 {x} = ind𝟚 (λ x → Eq𝟚 x x) triv triv x

cong𝟚 : {x y : 𝟚}{f : 𝟚 → 𝟚} → Eq𝟚 x y → Eq𝟚 (f x) (f y)
cong𝟚 {x} {y} {f} = λ eq₀ → transp𝟚 {x} {y} {λ b → Eq𝟚 (f x) (f b)}
  eq₀
  refl𝟚

ass∨₁ ass∨₂ : (x y z : 𝟚) → Eq𝟚 ((x ∨ y) ∨ z) (x ∨ (y ∨ z))
ass∨₁ x y z = ind𝟚 (λ x → Eq𝟚 ((x ∨ y) ∨ z) (x ∨ (y ∨ z)))
  triv
  (ind𝟚 (λ z → Eq𝟚 (ff ∨ y ∨ z) (ff ∨ (y ∨ z)))
    (trans𝟚 {(ff ∨ y) ∨ tt} {y ∨ tt} {ff ∨ (y ∨ tt)}
      (cong𝟚 {ff ∨ y} {y} {λ b → b ∨ tt}
        (idl∨ y))
      (sym𝟚 {(ff ∨ (y ∨ tt))} {(y ∨ tt)} ( idl∨ (y ∨ tt) )))
    (ind𝟚 (λ y → Eq𝟚 (ff ∨ y ∨ ff) (ff ∨ (y ∨ ff)))
      triv
      triv
      y)
    z)
  x
ass∨₂ = λ a b c → ind𝟚 (λ a → Eq𝟚 ((a ∨ b) ∨ c) (a ∨ (b ∨ c)))
                         triv
                         refl𝟚
                         a

{-
ass : (a b c : ℕ) → Eqℕ ((a + b) + c) (a + (b + c))
ass = ?
-}
