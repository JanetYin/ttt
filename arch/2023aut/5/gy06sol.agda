open import Lib

                          -- λ b -> if b then A else B
Σ=⊎ : {A B : Set} → Σ Bool (if_then A else B) ↔ A ⊎ B
-- fst Σ=⊎ (b , x) = {!if b then (inl x) else (inr x)!}
fst Σ=⊎ (false , x) = inr x
fst Σ=⊎ (true , x) = inl x
snd Σ=⊎ (inl a) = true , a
snd Σ=⊎ (inr b) = false , b

Σ=× : {A B : Set} → Σ A (λ _ → B) ↔ A × B
fst Σ=× (a , b) = a , b
snd Σ=× (a , b) = a , b

-- Π A F is essentially (a : A) → F a
-- what döes this mean?

                    -- Π A (λ _ → B)
Π=→ : {A B : Set} → ((a : A) → (λ _ → B) a) ≡ (A → B)
Π=→ = refl

                    -- Π Bool (if_then A else B)
→=× : {A B : Set} → ((b : Bool) → if b then A else B) ↔ A × B
fst →=× f = f true , f false
snd →=× (a , b) = λ {true -> a; false -> b}

dependentCurry : {A : Set}{B : A → Set}{C : (a : A) → B a → Set} →
  ((a : A)(b : B a) → C a b) ↔ ((w : Σ A B) → C (fst w) (snd w))
fst dependentCurry f (a , b) = f a b
snd dependentCurry g a b = g (a , b)


∀×-distr  : {A : Set}{P : A → Set}{Q : A → Set} → ((a : A) → P a × Q a)
               ↔ ((a : A) → P a) × ((a : A) → Q a)
∀×-distr = {!!}

{-
Bool
true, false

Fin 2
zero {1}, suc zero
-}

Bool=Fin2 : Bool ↔ Fin 2
fst Bool=Fin2 = λ {true -> zero; false -> suc zero}
snd Bool=Fin2 = λ {zero -> true; (suc zero) -> false}

{-
Fin 4:
zero, suc zero, suc (suc zero), suc (suc (suc zero))

Fin 1 ⊎ Fin 3:
inl zero, inr zero, inr (suc zero), inr (suc (suc zero))
-}

Fin1+3=Fin4 : Fin (1 + 3) ↔ Fin 1 ⊎ Fin 3
Fin1+3=Fin4 = {!!}

-- relating Fin m ⊎ Fin n and Fin (m + n)

inj₁f : {m n : ℕ} → Fin m → Fin (m + n)
inj₁f = {!!}

test-inj₁f : inj₁f {3}{4} (suc (suc zero)) ≡ suc (suc zero)
test-inj₁f = refl

inj₂f : {m n : ℕ} → Fin n → Fin (m + n)
inj₂f {m} i = {!!}

test-inj₂f : inj₂f {3}{4} (suc (suc zero)) ≡ suc (suc (suc (suc (suc zero))))
test-inj₂f = refl

f : {m n : ℕ} → Fin m ⊎ Fin n → Fin (m + n)
f (inl i) = inj₁f i
f (inr i) = inj₂f i

-- now backwards
f⁻¹ : {m n : ℕ} → Fin (m + n) → Fin m ⊎ Fin n   -- \^- \^1
f⁻¹ {m} i = {!!}

-- use f⁻¹
-- this essentially merges finite sequences
casef : {m n : ℕ}{C : Set} → (Fin m → C) → (Fin n → C) → Fin (m + n) → C
casef {m}  g h i   = {!!}

test-casef : casef {3}{3} (λ i → i) (λ i → i) (suc (suc zero)) ≡ suc (suc zero)
test-casef = refl
test-casef' : casef {3}{3} (λ i → i) (λ i → i) (suc (suc (suc zero))) ≡ zero
test-casef' = refl
test-casef'' : casef {3}{3} (λ i → i) (λ i → i) (suc (suc (suc (suc zero)))) ≡ suc zero
test-casef'' = refl

Fin+ : {m n : ℕ} → Fin (m + n) ↔ Fin m ⊎ Fin n
fst Fin+ = f⁻¹
snd Fin+ = f

-- this might be hard
Fin* : {m n : ℕ} → Fin (m * n) ↔ Fin m × Fin n
Fin* = {!!}

-- n-1
--  Σ  a i = a 0 + a 1 + ... + a (n-1)
-- i=0

Σℕ : (n : ℕ) → (Fin n → ℕ) → ℕ
Σℕ zero f = zero
Σℕ (suc n) f = f zero + Σℕ n (λ i -> f (suc i))

-- not very easy
Σ+ : (n : ℕ)(a : Fin n → ℕ) → Σ (Fin n) (λ i → Fin (a i)) ↔ Fin (Σℕ n a)
Σ+ = {!!}

-- n-1
--  Π  a i = a 0 * a 1 * ... * a (n-1)
-- i=0

Πℕ : (n : ℕ) → (Fin n → ℕ) → ℕ
Πℕ zero    a = 1
Πℕ (suc n) a = a zero * Πℕ n (λ i → a (suc i))

-- not very easy
Π* : (n : ℕ)(a : Fin n → ℕ) → ((i : Fin n) → Fin (a i)) ↔ Fin (Πℕ n a)
Π* = {!!}
