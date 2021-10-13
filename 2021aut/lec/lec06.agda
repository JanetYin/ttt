open import lib

f : {X : Set} → X → X ⊎ (X ⊎ X)
-- f = λ x → ι₁ x
-- f = λ x → ι₂ (ι₁ x)
f = λ x → ι₂ (ι₂ x)

-- A = X ⊎ Y → X
{-
IGAZ  Van olyan X és Y típus, melyre létezik t : A. pl. X=⊤
HAMIS Minden X-re és Y-ra létezik t : A. X:=⊥  Y:=⊤
     (⊥ ⊎ ⊤ → ⊥)  ↔ (⊤ → ⊥) ↔ ⊥
IGAZ Van olyan X és Y típus, melyre létezik t : ¬ A.
     (X ⊎ Y → X) → ⊥     X:=⊥  Y:=⊤ -}
     
g : (⊥ ⊎ ⊤ → ⊥) → ⊥
g = λ w → w (ι₂ triv)
-- HAMIS Minden X-re és Y-ra létezik t : ¬ A.
h : {X : Set} → ¬ (¬ (X ⊎ X → X))
h = λ w → w λ xvx → case xvx (λ x → x) (λ x → x)

{-
⊤ → (⊥ → ⊥)   ↔    ⊥ → ⊥    ↔    ⊤
⊥ → (⊤ → ⊥)   ↔    ⊤
⊥ → (⊤ → ⊤)   ↔    ⊤
(⊤ → ⊥) → ⊥   ↔    ⊥ → ⊥    ↔    ⊤
(⊥ → ⊤) → ⊥   ↔    ⊤ → ⊥    ↔    ⊥
-}
dd : (⊤ → ⊥) → ⊥
dd = λ w → w triv

ekv : {A : Set} → (⊤ → A) ↔ A
ekv = (λ w → w triv) , λ a _ → a

ekv' : {A B C : Set} → (A ↔ B) → ((A → C) ↔ (B → C))
ekv' = λ a↔b → (λ ac b → ac (π₂ a↔b b)) , λ bc a → bc (π₁ a↔b a)

dd' : (⊤ → ⊥) → ⊥
dd' = π₂ (ekv' ekv) (λ x → x)

{-
pl. ha A ↔ B, akkor A × C ↔ B × C
pl. ha A → B, akkor A × C → B × C
pl. ha A → B, akkor C × A → C × B
× mindket parametereben kovarians
⊎ ugyanigy
pl. ha B → A, akkor (A → C) → (B → C)
pl. ha A → B, akkor (C → A) → (C → B)    → az 1. parametereben kontravarians, masodik parametereben kovarians
-}

-- eddig: lenyegileg Haskell, iteletlogika
-- most: atterunk Agda, elsorendu logika

-- univerzumok
-- tt : 𝟚 , ff : 𝟚, 𝟚 : Set   <- Set az a tipusok tipusa

_^2 : Set → Set
_^2 = λ A → A × A

-- negyzet' : ℕ → ℕ
-- negyzet' = λ n → n * n

_^_ : Set → ℕ → Set
_^_ = λ A n → rec ⊤ (_× A) n

-- hatv A 10 = A × A × A × .... × A

-- rec u v n     u=⊤   v=(_× A)
-----------------------------------
-- hatv A zero = ⊤                        u
-- hatv A 1    = ⊤ × A   ↔   A            v u
-- hatv A 2    = (⊤ × A) × A              v (v u)
-- hatv A 3    = (⊤ × A × A) × A          v (v (v u))
-- hatv A 4    = ((⊤ × A × A) × A) × A    v (v (v (v u)))

pred : ℕ → ℕ ⊎ ⊤ -- Either ℕ (),  Maybe ℕ
pred = rec (ι₂ triv) λ x → case x (λ n → ι₁ (suc n)) (λ _ → ι₁ 0)
{-
     n    rec u v n
pred 0    ι₂ triv     u  
pred 1    ι₁ 0        v u
pred 2    ι₁ 1        v (v u)
pred 3    ι₁ 2        v (v (v u))
pred 4    ι₁ 3        v (v (v (v u))

v mukodese:   v (ι₁ n)    = ι₁ (suc n)
              v (ι₂ triv) = ι₁ 0
-}

eq0 : ℕ → 𝟚
eq0 = λ n → rec tt (λ _ → ff) n

eqℕ : ℕ → ℕ → 𝟚
eqℕ = rec eq0 (λ f x → case (pred x) (λ n → f n) (λ _ → ff))
{-
          rec eq0 (λ f x → f (pred x))
          rec eq0 (λ f x → case (pred x) (λ n → f n) (λ _ → ff))
eqℕ 0     eq0                       u
eqℕ 1     eq0∘pred                  v u
eqℕ 2     eq0∘pred∘pred             v (v u)
eqℕ 3     eq0∘pred∘pred∘pred        v (v (v u))
-}

eqN : ℕ → ℕ → 𝟚
eqN zero zero = tt
eqN (suc _) zero = ff
eqN zero (suc _) = ff
eqN (suc a) (suc b) = eqN a b

{-
_+_ : ℕ → ℕ → ℕ
zero + zero = zero
zero + suc b = suc b
suc a + zero = suc a
suc a + suc b = suc (suc (a + b))
_+_ : ℕ → ℕ → ℕ
_+_ = λ a b → rec b suc a
-}
_+_ : ℕ → ℕ → ℕ
zero  + b = b   --  rec b suc zero = b
suc n + b = suc (n + b) -- rec b suc (suc n) = suc (rec b suc n) = suc (n + b)

--------------------------------------------------------

-- zero + a = a
-- a + zero = a

-- belso egyenloseg, egyenloseg tipus, propozicionalis egyenloseg
-- kulso egyenloseg, definicio szerinti, =, judgemental equality

-- eqℕ : ℕ → ℕ → 𝟚
-- eqℕ 100 32 : 𝟚

-- Eqℕ 100 a : Set

Eqℕ : ℕ → ℕ → Set
Eqℕ = λ a b → if (eqN a b) then ⊤ else ⊥

100= : Eqℕ 100 100
100= = triv

100≠101 : ¬ Eqℕ 100 101 -- = Eqℕ 100 101 → ⊥ = ⊥ → ⊥
100≠101 = λ x → x
