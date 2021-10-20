module 2021aut.lec.lec07 where

open import lib

f : Set → Set → Set
f = λ A B → A × B

g1 g2 g3 g4 : {A : Set} → A × A → A ⊎ A
g1 = λ aa → ι₁ (π₁ aa)
g2 = λ aa → ι₁ (π₂ aa)
g3 = λ aa → ι₂ (π₁ aa)
g4 = λ aa → ι₂ (π₂ aa)

Eqℕ : ℕ → ℕ → Set
Eqℕ zero zero = ⊤
Eqℕ (suc a) (suc b) = Eqℕ a b
Eqℕ _ _ = ⊥

_+_ : ℕ → ℕ → ℕ
zero + b = b
suc a + b = suc (a + b)

{-
((⊤ × 𝟚) × 𝟚) × 𝟚

→     ha A : Set, B : A → Set, akkor (x : A) → B x : Set
         ℕ        B : ℕ → Set        (x : ℕ) → Eqℕ x (suc x)
                  B = λ n → Eqℕ n (suc n)
                  B 0 = Eqℕ 0 1
                  B 1 = Eqℕ 1 2
                  B 2 = Eqℕ 2 3
                  ...
         A = Set  B : Set → Set     ((x : A) → B x) = (X : Set) → X → X
                  B = λ X → X → X

        ha t : B x, felteve, hogy x : A, akkor λ x → t : (x : A) → B x
        ha t : (x : A) → B x, u : A, akkor t u : B u
        ha t : (x : ℕ) → Eqℕ x (suc x), akkor t 4 : Eqℕ 4 5
        ha t : (X : Set) → X → X, akkor t (⊤ ⊎ ⊥) : (⊤ ⊎ ⊥) → (⊤ ⊎ ⊥)
        szamitasi: (λ x → t) u = t-ben x elofordulasai u-ra helyettesitve
        egyediseg: (λ x → t x) = t

  f : (A : Set) → (B : Set) → (A × B) ↔ (B × A)
  f = λ A → λ B → (λ w → (π₂ w , π₁ w)) , (λ w → (π₂ w , π₁ w))

  implicit parameter

  g : {A B : Set} → (A × B) ↔ (B × A)
  g = λ {A}{B} → (λ w → (π₂ w , π₁ w)) , (λ w → (π₂ w , π₁ w))

  t : {x : 𝟚} → if x then ℕ × ℕ else ℕ
  t {ff} + 3

  (x y : A) → B x  = (x : A) → ((y : A) → B x) = (x : A)(y : A) → B x

  t : (x : _) → Eqℕ x (suc x) -- ∀ x. x=1+x   (alahuzas ket hasznalatat ismerjuk)
      ∀ x     → ...
      (x : ℕ) →
      ∀(x : ℕ) → 
    (λ _ → tt) : ℕ → 𝟚


  Eqℕ : ℕ → ℕ → Set         <- homogen binaris relacio ℕ-en

  A → B   = (x : A) → (λ _ → B) x = (x : A) → B

  -- →    fuggvenyter, implikacio (logikai kovetkeztetes), ∀ (univerzalis kvantor), Π
  -- Π_(n∈ℕ)(ℝ^{x*n}) = (n : ℕ) → Matrix n n
  Matrix : ℕ → ℕ → Set

_×_ : Set → Set → Set
  Σ : (A : Set) → (B : A → Set) → Set
  _,_   Ha u : A, v : B, akkor u,v : A × B
        Ha u : A, v : B u, akkor u,v : Σ A B
        _,_ : (x : A) → B x → Σ A B
  π₁    Σ A B → A
  π₂ :  (w : Σ A B) → B (π₁ w)
      π₁ (a,b)=a    π₂(a,b) = b      b : B a
                       (a,b) : Σ A B
                      π₂(a,b) : B (π₁ (a,b)) = B a
-}

w : Σ ℕ (λ n → Eqℕ (suc zero + n) (suc (suc (suc zero))))
w = 2 , triv

gg : (¬ ¬ Σ ℕ λ x → ⊤) → ℕ
gg = λ w → exfalso (w λ v → {!!})

-- A × B := Σ A (λ _ → B)
-- Σ-val megkapjuk: Descartes szorzat, logikai es, letezik, fuggo par  g:Σ(n∈ℕ).ℝ^[n×n]

{-
𝟚, tt, ff     ind𝟚 : (P : 𝟚 → Set) → P tt  → P ff                        → (b : 𝟚) → P b
              ind𝟚 P t f tt = t
              ind𝟚 P t f ff = f
ℕ, zero, suc  indℕ : (P : ℕ → Set) → P zero → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
              indℕ P z s zero = z
              indℕ P z s (suc n) = s n (indℕ P z s n)
              rec  :                 A      → (          A   → A)         →      ℕ  → A
              rec z s n = indℕ (λ _ → A) z (λ n pn → s pn) n
⊎, ι₁, ι₂     ind⊎ : (P : A ⊎ B → Set) → ((a : A)→P (ι₁ a))→((b : B)→P(ι₂ b)) → (w : A ⊎ B) → P w
              ind⊎ P u v (ι₁ a) = u a
              ind⊎ P u v (ι₂ b) = v b

R ⊂ A × B
R : A → B → Set
P : A → Set (unaris relacio, predikatum)
P n = (n+1 egyenlo 3-mal) = Eqℕ (n + 1) 3
P : 𝟚 → Set
P b = if b then ⊤ else ⊥
P tt = ⊤
P ff = ⊥
-}

Eq𝟚 : 𝟚 → 𝟚 → Set
Eq𝟚 tt tt = ⊤
Eq𝟚 tt ff = ⊥
Eq𝟚 ff tt = ⊥
Eq𝟚 ff ff = ⊤

not : 𝟚 → 𝟚
not x = if x then ff else tt

-- ind𝟚 : (P : 𝟚 → Set) → P tt  → P ff                        → (b : 𝟚) → P b

notnot : (x : 𝟚) → Eq𝟚 (not (not x)) x
notnot = ind𝟚 (λ x → Eq𝟚 (not (not x)) x) triv triv

-- HF: Σ tipust data-val megadni, _,_, π₁, π₂ operatorokat megadni, szamitasi szabalyokat ellenorizni

