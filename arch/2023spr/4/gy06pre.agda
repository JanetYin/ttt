open import lib

data Fin : ℕ → Set where  -- Fin n = n-elemu halmaz
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)


Σ=⊎ : ∀ {i} {A : Set i} {B : Set i} → Σ Bool (if_then A else B) ↔ A ⊎ B
Σ=⊎ = {!!}

Σ=× : ∀ {i j} {A : Set i} {B : Set j} → Σ A (λ _ → B) ↔ A × B
Σ=× = {!!}

-- ez a kettő tényleg ugyanaz a típus (vegyük észre, hogy _≡_ van _↔_ helyett)
Π≡→ : ∀ {i j} {A : Set i} {B : Set j} → ((a : A) → (λ _ → B) a) ≡ (A → B)
Π≡→ = {!!}

→=× : ∀ {i} {A : Set i} {B : Set i} → ((b : Bool) → if b then A else B) ↔ A × B
→=× = {!!}

-- az egyik két külön 
dependentCurry : {A : Set}{B : A → Set}{C : (a : A) → B a → Set} →
  ((a : A)(b : B a) → C a b) ↔ ((w : Σ A B) → C (fst w) (snd w))
dependentCurry = {!!}

∀×-distr  : ∀ {i j k}{A : Set i}{P : A → Set j}{Q : A → Set k} → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
∀×-distr = {!!}

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
