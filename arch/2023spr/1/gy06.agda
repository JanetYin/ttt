module gy06 where

open import lib

data Fin : ℕ → Set where  -- Fin n = n-elemu halmaz
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)


Σ=⊎ : {A B : Set} → Σ Bool (λ b → if b then A else B) ↔ A ⊎ B
Σ=⊎ = to , from where
  to : {A B : Set} → Σ Bool (λ b → if b then A else B) → A ⊎ B
  to (false , ab) = inr ab
  to (true , ab) = inl ab

  from : {A B : Set} → A ⊎ B → Σ Bool (λ b → if b then A else B)
  from (inl x) = true , x
  from (inr x) = false , x

Σ=× : {A B : Set} → Σ A (λ _ → B) ↔ A × B
Σ=× = to , from where
  to : {A B : Set} → Σ A (λ _ → B) → A × B
  to (a , b) = a , b

  from : {A B : Set} → A × B → Σ A (λ _ → B)
  from (a , b) = a , b

-- Π(a : A) : B a
Π=→ : {A B : Set} → ((a : A) → (λ _ → B) a) ≡ (A → B)
Π=→ = refl

{-
   Π     Σ
  / \   / \
 /   \ /   \
→     ×     ⊎
-}

→=× : {A B : Set} → ((b : Bool) → if b then A else B) ↔ A × B
→=× = to , from where
  to : {A B : Set} → ((b : Bool) → if b then A else B) → A × B
  to f = f true , f false

  from : {A B : Set} → A × B → ((b : Bool) → if b then A else B)
  from (a , b) false = b
  from (a , b) true = a
  
dependentCurry : {A : Set}{B : A → Set}{C : (a : A) → B a → Set} →
  ((a : A)(b : B a) → C a b) ↔ ((w : Σ A B) → C (fst w) (snd w))
dependentCurry = {!!}

-- ∀P ∀Q ((∀a(P(a) ∧ Q(a)) ↔ ∀aP(a) ∧ ∀aQ(a))
∀×-distr  : {A : Set}{P : A → Set}{Q : A → Set} → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
∀×-distr = to , from where
  to : {A : Set}{P : A → Set}{Q : A → Set} → ((a : A) → P a × Q a) → ((a : A) → P a) × ((a : A) → Q a)
  to f = (λ a → fst (f a)) , λ a → snd (f a)

  from : {A : Set}{P : A → Set}{Q : A → Set} → ((a : A) → P a) × ((a : A) → Q a) → ((a : A) → P a × Q a)
  from (f , g) a = f a , g a
  
Bool=Fin2 : Bool ↔ Fin 2
Bool=Fin2 = {!!}

Fin1+3=Fin4 : Fin (1 + 3) ↔ Fin 1 ⊎ Fin 3
Fin1+3=Fin4 = {!!}

-- relating Fin m ⊎ Fin n and Fin (m + n)

inj₁f : {m n : ℕ} → Fin m → Fin (m + n)
inj₁f i = {!!}

test-inj₁f : inj₁f {3}{4} (suc (suc zero)) ≡ suc (suc zero)
test-inj₁f = refl

inj₂f : {m n : ℕ} → Fin n → Fin (m + n)
inj₂f {m}  i = {!!}

test-inj₂f : inj₂f {3}{4} (suc (suc zero)) ≡ suc (suc (suc (suc (suc zero))))
test-inj₂f = refl

f : {m n : ℕ} → Fin m ⊎ Fin n → Fin (m + n)
f (inl i) = inj₁f i
f (inr i) = inj₂f i

casef : {m n : ℕ}{C : Set} → (Fin m → C) → (Fin n → C) → Fin (m + n) → C
casef {m}  f g i       = {!!}

test-casef : casef {3}{3} (λ i → i) (λ i → i) (suc (suc zero)) ≡ suc (suc zero)
test-casef = refl
test-casef' : casef {3}{3} (λ i → i) (λ i → i) (suc (suc (suc zero))) ≡ zero
test-casef' = refl
test-casef'' : casef {3}{3} (λ i → i) (λ i → i) (suc (suc (suc (suc zero)))) ≡ suc zero
test-casef'' = refl

-- use inj₁f,inj₂f in one direction and "casef inj₁ inj₂" in the other direction
Fin+ : {m n : ℕ} → Fin (m + n) ↔ Fin m ⊎ Fin n
Fin+ = {!!}

-- this might be hard
Fin* : {m n : ℕ} → Fin (m * n) ↔ Fin m × Fin n
Fin* = {!!}

-- n-1
--  Σ  a i = a 0 + a 1 + ... + a (n-1)
-- i=0

Σℕ : (n : ℕ) → (Fin n → ℕ) → ℕ
Σℕ zero    a = 0
Σℕ (suc n) a = a zero + Σℕ n (λ i → a (suc i))

-- not very easy
Σ+ : (n : ℕ)(a : Fin n → ℕ) → Σ (Fin n) (λ i → Fin (a i)) ↔ Fin (Σℕ n a)
Σ+ = {!!}

-- n-1
--  Π  a i = a 0 * a 1 * ... * a (n-1)
-- i=0

Πℕ : (n : ℕ) → (Fin n → ℕ) → ℕ
Πℕ zero    a = 0
Πℕ (suc n) a = a zero * Πℕ n (λ i → a (suc i))

-- not very easy
Π* : (n : ℕ)(a : Fin n → ℕ) → ((i : Fin n) → Fin (a i)) ↔ Fin (Πℕ n a)
Π* = {!!}
