{-# OPTIONS --guardedness #-}

module ea11 where

open import lib

-- Ez az előadás 13 perccel rövidebb.

-- vizsgak: majdnem minden szerdan 10-12 kozott MI laborban, gepteremben, peldavizsga

-- induktiv tipusok konstrukoratinak injektivitasa, diszjunktsaga, egyenloseg eldonthetosege

data T : Set where
  c1 : ℕ → Bool → T → T
  c2 : ℕ → T → T → T

Injective Injective-klasszikus : {A B : Set} → (A → B) → Set
Injective {A} f = {x y : A} → f x ≡ f y → x ≡ y
Injective-klasszikus {A} f = ¬ (Σ A λ x → Σ A λ y → ¬ (x ≡ y) → f x ≡ f y)

-- HF : Injective -> klasszikus, forditott irany fuggetlen

open import ea08 using (subst; sym)
open import ea09 using (cong)

suc-inj : {n n' : ℕ} → 1 + n ≡ 1 + n' → n ≡ n'
suc-inj e = cong pred e

c1-inv : T → ℕ
c1-inv (c1 n _ _) = n
c1-inv (c2 _ _ _) = 3

c1-inj1 : {n n' : ℕ}{b b' : Bool}{t t' : T} → c1 n b t ≡ c1 n' b' t' → n ≡ n'
c1-inj1 e = cong c1-inv e

-- induktiv tipus osszes konstruktora annak osszes parametereben injektiv

-- konstruktorok diszjunktak:

disj-ℕ-zero-suc : {n : ℕ} → ¬ (zero ≡ suc n)
disj-ℕ-zero-suc e = subst P e tt
  where
    P : ℕ → Set
    P zero = ⊤
    P (suc _) = ⊥

disj-T-c1-c2 : {n n' : ℕ}{b : Bool}{t t' t'' : T} → ¬ (c1 n b t ≡ c2 n' t' t'')
disj-T-c1-c2 e = subst P e tt
  where
    P : T → Set
    P (c1 _ _ _) = ⊤
    P (c2 _ _ _) = ⊥

-- egyenloseg eldonthetosege

Decidable : Set → Set
Decidable A = A ⊎ ¬ A

ind⊎ : {A B : Set}(P : A ⊎ B → Set) → ((a : A) → P (inl a))
       → ((b : B) → P (inr b)) → (w : A ⊎ B) → P w
ind⊎ P l r (inl x) = l x
ind⊎ P l r (inr x) = r x

dec-ℕ : (n n' : ℕ) → Decidable (n ≡ n')
dec-ℕ zero zero = inl refl
dec-ℕ zero (suc n') = inr disj-ℕ-zero-suc
dec-ℕ (suc n) zero = inr λ e → disj-ℕ-zero-suc (sym e)
dec-ℕ (suc n) (suc n') = case (dec-ℕ n n')
  (λ e → inl (cong suc e))
  λ n≠n' → inr λ e → n≠n' (suc-inj e)

-- HF: dec-T

data T' : Set where
  c1 : T'
  c2 : (ℕ → T') → T'

-- vegesen elagozodo induktiv tipusok egyenlosege eldontheto

-- kotermeszetes szamok, osszeadas

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A

zeros : Stream ℕ
Stream.head zeros = 0
Stream.tail zeros = zeros

-- Hilbert es Brouwer vitaja (1920 korul), 1960as evekben Bishop
-- Gödel double negation translation:
-- (A ∧ B) klasszikus bizonyitasa az nem mas, mint ¬ ¬ A ∧ ¬ ¬ B konstruktiv bizonyitasa
-- klassz vs konstr (√2)^(log_2(9)))

-- letezik a,b irracionalis szam, es a^b racionalis

-- klasszikus: a:=b:=sqrt(2). ket eset van:
-- 1. sqrt(2)^(sqrt(2)) racionalis, akkor keszen vagyunk
-- 2. sqrt(2)^(sqrt(2)) irracionalis, a:=sqrt(2)^(sqrt(2)), b := sqrt(2)
--    (sqrt(2)^(sqrt(2)))^(sqrt(2)) = ((2^0.5)^(2^0.5))^(2^0.5) = (2^0.5)^((2^0.5)*(2^0.5)) = 2

-- konstruktiv: a:= (√2)  b:= (log_2(9)))  2^(log_2(9)) = 3

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just : A → Maybe A

record ℕ∞ : Set where
  coinductive
  field
    pred∞ : Maybe ℕ∞
open ℕ∞

zero∞ : ℕ∞
pred∞ zero∞ = Nothing

one∞ : ℕ∞
pred∞ one∞ = Just zero∞

∞ : ℕ∞
pred∞ ∞ = Just ∞

_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
a +∞ b = {!!}

-- tipusok egyenlosege: Bool ≡ ⊤ ⊎ ⊤, viszont
-- Bool ≠ ⊤
--  ^ HF
