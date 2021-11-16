module 2021aut.t2.gy08.pred-solved where
open import lib

infixr 0 _$_
_$_ : ∀{i j}{A : Set i}{B : Set j} → (A → B) → A → B
f $ a = f a
const : ∀{i j} → {X : Set i}{Y : Set j} → X → Y → X
const x = λ _ → x
_or_ : ∀{i j k} → {X : Set i}{Y : Set j}{Z : Set k} → (X → Z) → (Y → Z) → X ⊎ Y → Z
x or y = λ t → case t x y
id : ∀{i} → {X : Set} → X → X
id x = x

∀×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
∀×-distr A = λ P Q → _,_
  (λ f → (λ a → π₁ (f a)) , λ a → π₂ (f a))
  (λ { (f , g) a → f a , g a })
∀⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a) ⊎ ((a : A) → Q a) → ((a : A) → P a ⊎ Q a)
∀⊎-distr A P Q = (λ f a → ι₁ (f a)) or λ f a → ι₂ (f a)
Σ×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a × Q a)  → Σ A P × Σ A Q
Σ×-distr A P Q = λ {(a , (pa , qa)) → (a , pa) , (a , qa)}
Σ⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a)  ↔ Σ A P ⊎ Σ A Q
Σ⊎-distr A P Q = _,_
  (λ {(a , paqa) → case paqa (λ pa → ι₁ (a , pa)) (λ qa → ι₂ (a , qa))})
  ((λ {(a , pa) → a , ι₁ pa}) or λ {(a , qa) → a , ι₂ qa})
¬∀        :    (A : Set)(P : A → Set)              → (Σ A λ a → ¬ P a)      → ¬ ((a : A) → P a)
¬∀ A P lem1 = λ lem2 → let
  (a , npa) = lem1
  pa = lem2 a
  in npa pa
¬Σ        :    (A : Set)(P : A → Set)              → (¬ Σ A λ a → P a)      ↔ ((a : A) → ¬ P a)
¬Σ A P = _,_
  (λ nΣAP a → λ pa → nΣAP (a , pa))
  (λ lem → λ {(a , pa) → lem a pa})
⊎↔ΣBool   :    (A B : Set)                         → (A ⊎ B)                ↔ Σ 𝟚 (λ b → if b then A else B)
⊎↔ΣBool A B = _,_
  (_,_ tt or _,_ ff)
  (λ { (b , p) →  ind𝟚 (λ b → if b then A else B → A ⊎ B) ι₁ ι₂ b p})
¬¬∀-nat   :    (A : Set)(P : A → Set)              → ¬ ¬ ((x : A) → P x)    → (x : A) → ¬ ¬ (P x)
¬¬∀-nat A P nnlem x = λ npx → nnlem λ lem → npx $ lem x

∀⊎-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (((a : A) → P a ⊎ Q a) → ((a : A) → P a) ⊎ ((a : A) → Q a)))
∀⊎-distr' = λ f → case (f ℕ isEven' isOdd everyℕisEvenOrOdd) (λ allEven → allEven 1) (λ allOdd → allOdd 0)
  where
    isEven : ℕ → 𝟚
    isEven = rec tt (λ b → if b then ff else tt)
    isEven' : ℕ → Set
    --isEven' n = if isEven n then ⊤ else ⊥
    isEven' 0 = ⊤
    isEven' 1 = ⊥
    isEven' (suc (suc n)) = isEven' n
    isOdd : ℕ → Set
    --isOdd n = if isEven n then ⊥ else ⊤
    isOdd 0 = ⊥
    isOdd 1 = ⊤
    isOdd (suc (suc n)) = isOdd n
    everyℕisEvenOrOdd : (n : ℕ) → isEven' n ⊎ isOdd n
    --everyℕisEvenOrOdd n = if isEven n then {!ι₁ triv!} else {!ι₂ triv!}
    everyℕisEvenOrOdd 0 = ι₁ triv
    everyℕisEvenOrOdd 1 = ι₂ triv
    everyℕisEvenOrOdd (suc (suc n)) = everyℕisEvenOrOdd n

Σ×-distr'₁ Σ×-distr'₂ Σ×-distr'₃ Σ×-distr'₄ : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (Σ A P × Σ A Q → Σ A λ a → P a × Q a))
Σ×-distr'₁ lem = let
  A = 𝟚
  P = ind𝟚 (λ _ → Set) ⊤ ⊥
  Q = ind𝟚 (λ _ → Set) ⊥ ⊤
  (a , b) = lem A P Q ((tt , triv) , (ff , triv))
  in ind𝟚 (λ a → P a × Q a → ⊥) π₂ π₁ a b
Σ×-distr'₂ lem = ind⊎ (λ a → P a × Q a → ⊥) (const $ λ {(pa , qa) → pa}) (const $ λ {(pa , qa) → qa}) a b
  where
    A = ⊤ ⊎ ⊤
    P : A → Set
    P = const ⊥ or const ⊤
    Q : A → Set
    Q = const ⊤ or const ⊥
    bad = (lem A P Q) ((ι₂ triv , triv) , (ι₁ triv , triv))
    a : A
    a = π₁ bad
    b : P a × Q a
    b = π₂ bad
Σ×-distr'₃ lem = ind𝟚 (λ a → P a × Q a → ⊥) π₂ π₁ a b
  where
    A = 𝟚
    P Q : A → Set
    P ff = ⊥
    P tt = ⊤
    Q ff = ⊤
    Q tt = ⊥
    a : A
    b : P a × Q a
    bad = lem A P Q ((tt , triv) , (ff , triv))
    a = π₁ bad
    b = π₂ bad
    pa : P a
    qa : Q a
    pa = π₁ b
    qa = π₂ b
Σ×-distr'₄ lem = ind⊎ (λ a → P a × Q a → ⊥) (const π₁) (const π₂) badA badProof
  where
    A = ⊤ ⊎ ⊤
    P Q : A → Set
    P = const ⊥ or const ⊤
    Q = const ⊤ or const ⊥
    l r : A
    l = ι₁ triv
    r = ι₂ triv
    badExample = lem A P Q ((r , triv) , (l , triv))
    badA = π₁ badExample
    badProof = π₂ badExample

Σ∀       : (A B : Set)(R : A → B → Set)        → (Σ A λ x → (y : B) → R x y) → (y : B) → Σ A λ x → R x y
Σ∀ A B R = λ {(a , f) y → (a , f y)}
AC       : (A B : Set)(R : A → B → Set)        → ((x : A) → Σ B λ y → R x y) → Σ (A → B) λ f → (x : A) → R x (f x)
AC A B R = λ f → ((λ a → π₁ (f a)) , λ a → π₂ (f a))

-- this is nice to prove:
Eq𝟚 : 𝟚 → 𝟚 → Set
Eq𝟚 tt tt = ⊤
Eq𝟚 tt ff = ⊥
Eq𝟚 ff tt = ⊥
Eq𝟚 ff ff = ⊤
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
exfalso𝟚 : {x : 𝟚} → ∀{i}{A : Set i} → Eq𝟚 x tt → Eq𝟚 x ff → A
exfalso𝟚 {x} = λ eq₁ eq₂ → exfalso (ind𝟚 (λ x → Eq𝟚 x tt → Eq𝟚 x ff → ⊥)
  (λ _ bot → bot)
  (λ bot _ → bot)
  x eq₁ eq₂)
cong𝟚 : {x y : 𝟚}{f : 𝟚 → 𝟚} → Eq𝟚 x y → Eq𝟚 (f x) (f y)
cong𝟚 {x} {y} {f} = λ eq₀ → transp𝟚 {x} {y} {λ b → Eq𝟚 (f x) (f b)}
  eq₀
  refl𝟚
3xf₁ 3xf₂ 3xf₃ : (f : 𝟚 → 𝟚)(x : 𝟚) → Eq𝟚 (f (f (f x))) (f x)
3xf₁ f x = case lem
  (_or_
    (λ eq → let
      lem₁ = ind𝟚 (λ x → Eq𝟚 (f x)         tt) (eq      tt)  (eq      ff)
      lem₂ = ind𝟚 (λ x → Eq𝟚 (f (f x))     tt) (lem₁ (f tt)) (lem₁ (f ff))
      lem₃ = ind𝟚 (λ x → Eq𝟚 (f (f (f x))) tt) (lem₂ (f tt)) (lem₂ (f ff))
      in trans𝟚 (lem₃ x) (sym𝟚 (lem₁ x)))
    λ eq → let
      lem₁ = λ x → ind𝟚 (λ x → Eq𝟚 (f x) x                  ) (eq tt) (eq ff) x
      in trans𝟚 (lem₁ (f (f x))) (lem₁ (f x))
    )
  (_or_
    (λ eq → let
      lem₀ : {x : 𝟚} → Eq𝟚 (f x) (not x)
      lem₀ {x} = eq x
      lem₁ : {x : 𝟚} → Eq𝟚 (f (f x)) (not (not x))
      lem₁ {x} = trans𝟚 {f (f x)} {f (not x)} {not (not x)}
        (ind𝟚 (λ f$x → Eq𝟚 (f x) f$x → Eq𝟚 (f (f$x)) (f (not x)))
          (λ eq₁ → ind𝟚 (λ not$x → Eq𝟚 (not x) not$x → Eq𝟚 (f tt) (f not$x))
            (λ _ → refl𝟚)
            (λ eq₂ → exfalso $ trans𝟚 (sym𝟚 eq₁) (trans𝟚 (eq x) eq₂))
            (not x) refl𝟚)
          (λ eq₁ → ind𝟚 (λ not$x → Eq𝟚 (not x) not$x → Eq𝟚 (f ff) (f not$x))
            (λ eq₂ → exfalso (trans𝟚 (sym𝟚 eq₁) (trans𝟚 (eq x) eq₂)))
            (λ _ → refl𝟚)
            (not x) refl𝟚)
          (f x) refl𝟚)
        (transp𝟚 {f x} {not x} {λ b → Eq𝟚 (f b) (not b)}
          lem₀
          lem₀)
      lem₂ : {x : 𝟚} → Eq𝟚 (not (not x)) x
      lem₂ {x} = ind𝟚 (λ x → Eq𝟚 (not (not x)) x) triv triv x
      in trans𝟚 (lem₁ {f x}) (lem₂ {f x}))
    λ eq → let
      lem₀ : {x : 𝟚} → Eq𝟚 (f x) ff
      lem₀ {x} = ind𝟚 (λ x → Eq𝟚 (f x) ff)
        (eq tt)
        (eq ff)
        x
      lem₁ = lem₀
      lem₂ = sym𝟚 lem₀
      in trans𝟚 {f (f (f x))} {ff} {f x} lem₁ lem₂
    )
  where
    id' not ct' cf' : 𝟚 → 𝟚
    ct' x = if x then tt else tt -- constant true
    id' x = if x then tt else ff -- pass as-is
    not x = if x then ff else tt -- negate
    cf' x = if x then ff else ff -- constant false
    Is = λ f₁ f₂ → ∀ (x : 𝟚) → Eq𝟚 (f₁ x) (f₂ x)
    LemL = Is f ct' ⊎ Is f id'
    LemR = Is f not ⊎ Is f cf'
    Lem = LemL ⊎ LemR
    lem : Lem
    lem = ind𝟚 (λ f$tt → Eq𝟚 (f tt) f$tt → Lem)
      (λ eqt → ι₁ (ind𝟚 (λ f$ff → Eq𝟚 (f ff) f$ff → LemL)
        (λ eqf → ι₁ λ b → ind𝟚 (λ b → Eq𝟚 (f b) (ct' b)) eqt eqf b)
        (λ eqf → ι₂ λ b → ind𝟚 (λ b → Eq𝟚 (f b) (id' b)) eqt eqf b)
        (f ff) (ind𝟚 (λ f$ff → Eq𝟚 f$ff f$ff) triv triv (f ff))))
      (λ eqt → ι₂ (ind𝟚 (λ f$ff → Eq𝟚 (f ff) f$ff → LemR)
        (λ eqf → ι₁ λ b → ind𝟚 (λ b → Eq𝟚 (f b) (not b)) eqt eqf b)
        (λ eqf → ι₂ λ b → ind𝟚 (λ b → Eq𝟚 (f b) (cf' b)) eqt eqf b)
        (f ff) (ind𝟚 (λ f$ff → Eq𝟚 f$ff f$ff) triv triv (f ff))))
      (f tt) (ind𝟚 (λ f$tt → Eq𝟚 f$tt f$tt) triv triv (f tt))
3xf₂ f x = ind𝟚 (λ x → Eq𝟚 (f (f (f x))) (f x))
  (ind𝟚 (λ f$tt → Eq𝟚 (f tt) f$tt → Eq𝟚 (f (f f$tt)) f$tt)
    (λ eq₁ → ind𝟚 (λ f$tt → Eq𝟚 (f tt) f$tt → Eq𝟚 (f f$tt) tt)
      (λ _ → eq₁)
      (λ eq₂ → exfalso (trans𝟚 {tt} {f tt} {ff}
        (sym𝟚 eq₁)
        eq₂))
      (f tt) refl𝟚)
    (λ eq₁ → ind𝟚 (λ f$ff → Eq𝟚 (f ff) f$ff → Eq𝟚 (f f$ff) ff)
      (λ _ → eq₁)
      (λ eq₂ → eq₂)
      (f ff) refl𝟚)
    (f tt) refl𝟚)
  (ind𝟚 (λ f$ff → Eq𝟚 (f ff) f$ff → Eq𝟚 (f (f f$ff)) f$ff)
    (λ eq₁ → ind𝟚 (λ f$tt → Eq𝟚 (f tt) f$tt → Eq𝟚 (f f$tt) tt)
      (λ eq₂ → eq₂)
      (λ _ → eq₁)
      (f tt) refl𝟚)
    (λ eq₁ → trans𝟚 {f (f ff)} {f ff} {ff}
      (ind𝟚 (λ f$ff → Eq𝟚 (f ff) f$ff → Eq𝟚 (f f$ff) f$ff)
        (λ eq₂ → exfalso (trans𝟚 {tt} {f ff} {ff}
          (sym𝟚 eq₂)
          eq₁))
        (λ eq₂ → eq₂)
        (f ff) refl𝟚)
      eq₁)
    (f ff) refl𝟚)
  x
3xf₃ f x = ind𝟚 (λ x' → Eq𝟚 x x' → Eq𝟚 (f (f (f x'))) (f x'))
  (λ eq₁ → ind𝟚 (λ f$tt → Eq𝟚 (f tt) f$tt → Eq𝟚 (f (f f$tt)) f$tt)
    (λ eq₂ → ind𝟚 (λ f$tt → Eq𝟚 (f tt) f$tt → Eq𝟚 (f f$tt) tt)
      (λ eq₃ → eq₃)
      (λ eq₃ → exfalso𝟚 eq₂ eq₃)
      (f tt) refl𝟚)
    (λ eq₂ → ind𝟚 (λ f$ff → Eq𝟚 (f ff) f$ff → Eq𝟚 (f f$ff) ff)
      (λ _ → eq₂)
      (λ eq₃ → eq₃)
      (f ff) refl𝟚)
    (f tt) refl𝟚)
  (λ eq₁ → ind𝟚 (λ f$ff → Eq𝟚 (f ff) f$ff → Eq𝟚 (f (f f$ff)) f$ff)
    (λ eq₂ → ind𝟚 (λ f$tt → Eq𝟚 (f tt) f$tt → Eq𝟚 (f f$tt) tt)
      (λ eq₃ → eq₃)
      (λ _ → eq₂)
      (f tt) refl𝟚)
    (λ eq₂ → ind𝟚 (λ f$ff → Eq𝟚 (f ff) f$ff → Eq𝟚 (f f$ff) ff)
      (λ eq₃ → exfalso𝟚 eq₃ eq₂)
      (λ _ → eq₂)
      (f ff) refl𝟚)
    (f ff) refl𝟚)
  x refl𝟚
