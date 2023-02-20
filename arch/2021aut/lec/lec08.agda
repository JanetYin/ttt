module 2021aut.lec.lec08 where

open import lib

-- elsőrendű logika példák (Tichler Krisztián)

-- 𝟚,ℕ, ×,⊎,⊥,⊤, →, Σ

{-
Nincs olyan használtautó-kereskedő, aki használt autót vásárolna a családjának.
Vannak olyan emberek, akik használt autót vásárolnak a családjuknak és nem becsületesek.
Tehát vannak olyan nem becsületes emberek, akik nem használtautó-kereskedők.
-}
module NEPPER (Ember : Set)(Keresk : Ember → Set)
  (Vasarol : Ember → Set)(Becsuletes : Ember → Set) where
  tetel : ¬ (Σ Ember λ e → Keresk e × Vasarol e) →
          (Σ Ember λ e → Vasarol e × ¬ (Becsuletes e)) →
          Σ Ember λ e → ¬ (Becsuletes e) × ¬ (Keresk e)
  tetel = λ A B → π₁ B , π₂ (π₂ B) , λ ker →
    A (π₁ B , ker , (π₁ (π₂ B)))

{-
A1 Minden egyetemista becsületes.
A2 János nem becsületes.
Tehát János nem egyetemista.
-}
module becsulet (X : Set)(E : X → Set)(B : X → Set)(j : X)
  (A1 : (x : X) → E x → B x)(A2 : ¬ B j) where
  tetel : ¬ E j
  tetel = λ ej → A2 (A1 j ej)

{-
Minden atléta erős.
Mindenki, aki erős és okos, az karrierre számı́that.
Péter atléta.
Péter okos.
Tehát Péter karrierre számı́that.
-}
module atletak
  (Ember : Set)(p : Ember)
  (Atleta Eros Okos Szamithat : Ember → Set)
  (A1 : (x : _) → Atleta x → Eros x)
  (A2 : ∀ x → Eros x × Okos x → Szamithat x)
  (A3 : Atleta p)
  (A4 : Okos p)
  where
  tetel : Szamithat p
  tetel = A2 p (A1 _ A3 , A4)

p1 : (A : Set)(P : A → Set)(Q : A → Set) →
-- (A → B × C) ↔ (A → B) × (A → C)
 ((a : A) → P a × Q a) ↔ ((a : A) → P a) × ((a : A) → Q a)
p1 = λ A P Q → (λ f → (λ a → π₁ (f a)) , {!!}) ,
  λ fg → λ a → (π₁ fg a) , (π₂ fg a)

p2 : (A : Set)(P : A → Set)(Q : A → Set) →
 ((a : A) → P a) ⊎ ((a : A) → Q a) → ((a : A) → P a ⊎ Q a)
p2 A P Q = λ w a → case w (λ f → ι₁ (f a)) (λ g → ι₂ (g a))

¬p2 : ¬ ((A : Set)(P : A → Set)(Q : A → Set) →
  ((a : A) → P a ⊎ Q a) → ((a : A) → P a) ⊎ ((a : A) → Q a))
¬p2 = λ w → case (w 𝟚 tt= ff= ttvff) (λ h → h ff) (λ h → h tt)
  where
    tt= ff= : 𝟚 → Set
    tt= = λ b → if b then ⊤ else ⊥
    ff= = λ b → if b then ⊥ else ⊤
    ttvff : (b : 𝟚) → tt= b ⊎ ff= b
    ttvff = ind𝟚 (λ b → tt= b ⊎ ff= b) (ι₁ triv) (ι₂ triv)

-- f injektiv, szurjektiv, konstans, (sz.)monoton no/csokken
-- ha egy f : 𝟚 → 𝟚 konstans, akkor nem szurjektiv

_=ℕ_ : ℕ → ℕ → Set
zero =ℕ zero = ⊤
zero =ℕ suc n = ⊥
suc m =ℕ zero = ⊥
suc m =ℕ suc n = m =ℕ n

_inj : (ℕ → ℕ) → Set
f inj = ∀ x y → f x =ℕ f y → x =ℕ y
-- ¬ (∃ x,y . x≠y → f x = f y)

{-          f
      ----------->
ert.tart.           ertekkeszlet
a ------------------->x
b                   /^y
c -----------------/  z
d                     x'
e                     y'
f
-}

_szurj : (ℕ → ℕ) → Set
f szurj = (y : ℕ) → Σ ℕ λ x → f x =ℕ y
infix 30 _szurj _inj

f = suc -- injektiv, de nem szurjektiv
finj : f inj
finj = λ x y e → e
-- (x y : ℕ) → f x =ℕ f y → x =ℕ y
-- (x y : ℕ) → suc x =ℕ suc y → x =ℕ y
-- (x y : ℕ) → x =ℕ y → x =ℕ y
¬fszurj : ¬ f szurj
¬fszurj = λ w → π₂ (w zero)
-- Σ ℕ (λ x → f x =ℕ zero)
-- Σ ℕ (λ x → suc x =ℕ zero)
-- Σ ℕ (λ _ → ⊥)
-- ℕ × ⊥

-- suc m =ℕ suc n = m =ℕ n

g : ℕ → ℕ
g zero = zero
g (suc zero) = zero
g (suc (suc n)) = suc (g (suc n))

¬ginj : ¬ g inj
¬ginj = λ w → w 0 1 triv

gszurj : g szurj
gszurj = indℕ (λ y → Σ ℕ (λ x → g x =ℕ y)) (1 , triv)
  (λ n ih → suc (π₁ ih) , {!π₂ ih!})


{-
kerdes ora vegen:
(A × A)   ≅   (𝟚 → A)
(A × B)   ≅   ((b : 𝟚) → if b then A else B)
A₀ × A₁ × A₂ .... ≅    ((i : I) → A i)   Π product
i=0 i=1 i=2 ....
-}
