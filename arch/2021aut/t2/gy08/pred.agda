module 2021aut.t2.gy08.pred where
open import lib

-- Helpers:
infixr 0 _$_
_$_ : ∀{i j}{A : Set i}{B : Set j} → (A → B) → A → B
f $ a = f a
const : ∀{i j} → {X : Set i}{Y : Set j} → X → Y → X
const x = λ _ → x
_or_ : ∀{i j k} → {X : Set i}{Y : Set j}{Z : Set k} → (X → Z) → (Y → Z) → X ⊎ Y → Z
x or y = λ t → case t x y
id : ∀{i} → {X : Set} → X → X
id x = x

-- Easy tasks:
∀×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
∀×-distr A P Q = {!!}
{- tut solution:
∀×-distr A = λ P Q → _,_
  (λ z → (λ x → π₁ (z x)) , (λ x → π₂ (z x)))
  λ f → λ a → (π₁ f) a , (π₂ f) a
-}
∀⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a) ⊎ ((a : A) → Q a) → ((a : A) → P a ⊎ Q a)
∀⊎-distr A P Q = {!!}
Σ×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a × Q a)  → Σ A P × Σ A Q
Σ×-distr A P Q fv = (a , π₁ t) , a , (π₂ t)
  where
  a : A
  a = π₁ fv
  t : P a × Q a
  t = π₂ fv
Σ⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a)  ↔ Σ A P ⊎ Σ A Q
Σ⊎-distr A P Q = _,_
  (λ t → case (π₂ t) (λ P$π₁$t → ι₁ ((π₁ t) , P$π₁$t)) λ Q$π₁$t → ι₂ ((π₁ t) , Q$π₁$t))
  (λ t → case t (λ ΣAP → (π₁ ΣAP) , (ι₁ $ π₂ ΣAP)) λ ΣAQ → (π₁ ΣAQ) , (ι₂ (π₂ ΣAQ)))
¬∀        :    (A : Set)(P : A → Set)              → (Σ A λ a → ¬ P a)      → ¬ ((a : A) → P a)
¬∀ A P lem1 = {!!}
¬Σ        :    (A : Set)(P : A → Set)              → (¬ Σ A λ a → P a)      ↔ ((a : A) → ¬ P a)
¬Σ A P = _,_
  (λ nt a → λ pa → nt ((a , {!!})))
  {!!}
-- Σ is just "×"
t : Σ 𝟚 (λ b → if b then 𝟚 else ℕ)
t = ff , 1
⊎↔ΣBool   :    (A B : Set)                         → (A ⊎ B)                ↔ Σ 𝟚 (λ b → if b then A else B)
⊎↔ΣBool A B = _,_
  {!!}
  λ t → let
    b = π₁ t
    in ind𝟚 (λ b → if b then A else B → (A ⊎ B))
      ι₁ -- A
      ι₂
      b (π₂ t)
¬¬∀-nat   :    (A : Set)(P : A → Set)              → ¬ ¬ ((x : A) → P x)    → (x : A) → ¬ ¬ (P x)
¬¬∀-nat A P nnlem x = {!!}

-- Defining isEven' and isOdd using pattern matching is the way to go
∀⊎-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (((a : A) → P a ⊎ Q a) → ((a : A) → P a) ⊎ ((a : A) → Q a)))
∀⊎-distr' = λ f → case (f ℕ isEven' isOdd everyℕisEvenOrOdd) (λ allEven → allEven 1) (λ allOdd → allOdd 0)
  where
    isEven : ℕ → 𝟚
    isEven = rec tt (λ b → if b then ff else tt)
    isEven' : ℕ → Set
    isEven' = {!!}
    isOdd : ℕ → Set
    isOdd = {!!}
    everyℕisEvenOrOdd : (n : ℕ) → isEven' n ⊎ isOdd n
    -- Technically indℕ can also be used, but this task is easy by pattern matching
    everyℕisEvenOrOdd = {!!}

Σ×-distr'₁ Σ×-distr'₂ Σ×-distr'₃ : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (Σ A P × Σ A Q → Σ A λ a → P a × Q a))
Σ×-distr'₁ lem = let
  A = 𝟚
  P = λ b → if b then ⊤ else ⊥
  Q = λ b → if b then ⊥ else ⊤
  badExample = lem A P Q ((tt , triv) , ((ff , triv)))
  a : 𝟚
  a = π₁ badExample
  b : P a × Q a
  {-
  a = tt
  P a = ⊤
  Q a = ⊥
  b : ⊤ × ⊥

  a = ff
  P a = ⊥
  Q a = ⊤
  b : ⊥ × ⊤
  -}
  b = π₂ badExample
  indBiz = ind𝟚 (λ a → (P a × Q a → ⊥))
    (π₂) -- (P tt = ⊤) × (Q tt = ⊥) → ⊥
    (π₁) -- (P ff = ⊥) × (Q ff = ⊤) → ⊥
    a
  in indBiz b
Σ×-distr'₂ lem = let
  A : Set
  A = {!!}
  P : A → Set
  P = {!!}
  Q : A → Set
  Q = {!!}
  suprise = lem A P Q ({!!} , {!!})
  in ind𝟚 (λ a → P a × Q a → ⊥)
    {!!}
    {!!}
    (π₁ suprise) {!suprise!}
Σ×-distr'₃ = {!!}

-- Easy again...
Σ∀       : (A B : Set)(R : A → B → Set)        → (Σ A λ x → (y : B) → R x y) → (y : B) → Σ A λ x → R x y
Σ∀ A B R = {!!}
AC       : (A B : Set)(R : A → B → Set)        → ((x : A) → Σ B λ y → R x y) → Σ (A → B) λ f → (x : A) → R x (f x)
AC A B R = {!!}

-- Some helpers:
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
{-
"=" reflexív:
∀ x : x = x
-}
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

-- Really hard
3xf₁ 3xf₂ : (f : 𝟚 → 𝟚)(x : 𝟚) → Eq𝟚 (f (f (f x))) (f x)
3xf₁ f x = ind𝟚 (λ f$x → Eq𝟚 (f x) f$x → Eq𝟚 (f (f (f$x))) (f$x))
  (λ eq-f$x → ind𝟚 (λ f$tt → Eq𝟚 (f tt) f$tt → Eq𝟚 (f f$tt) tt)
    (λ eq-f$tt → {!!})
    (λ eq-f$tt → ind𝟚 (λ f$ff → Eq𝟚 (f ff) f$ff → Eq𝟚 f$ff tt)
      {!!}
      {- For the following we have:
      eq-f$tt : Eq𝟚 (f tt) ff
      eq-f$ff : Eq𝟚 (f ff) ff
      (thus there's no such x, that Eq𝟚 (f x) tt, because for every x (tt and ff) we have Eq𝟚 (f x) ff (eq-f$tt and eq-f$ff, respectively)
      But:
      eq-f$x : Eq𝟚 (f x) tt
      Now we can do an induction on x, to prove for every x, that there's a contradiction (⊥):
      -}
      (λ eq-f$ff → {!ind𝟚 (λ x → ?)
        ?
        ?
        x!})
      {- p.s. for the above comment:
      We can do an indution on x, that ¬ Eq𝟚 (f ff) ff holds (λ eq-f$ff → ...)
      -}
      (f ff) refl𝟚)
    (f tt) refl𝟚)
  (λ eq-f$x → ind𝟚 (λ f$ff → Eq𝟚 (f ff) f$ff → Eq𝟚 (f f$ff) ff)
    {!!}
    {!!}
    (f ff) (refl𝟚))
  (f x) (refl𝟚)
3xf₂ f x = {!ind𝟚!}
