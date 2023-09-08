open import lib

data Fin : ℕ → Set where  -- Fin n = n-elemu halmaz
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)


Σ=⊎ : {A B : Set} → Σ Bool (if_then A else B) ↔ A ⊎ B
fst Σ=⊎ (false , ab) = inr ab
fst Σ=⊎ (true , ab) = inl ab
snd Σ=⊎ (inl x) = true , x
snd Σ=⊎ (inr x) = false , x

Σ=× : {A B : Set} → Σ A (λ _ → B) ↔ A × B
fst Σ=× (a , b) = a , b
snd Σ=× (a , b) = a , b

Π=→ : {A B : Set} → ((a : A) → (λ _ → B) a) ≡ (A → B)
Π=→ = refl

→=× : {A B : Set} → ((b : Bool) → if b then A else B) ↔ A × B
fst →=× x = x true , x false
snd →=× (a , b) false = b
snd →=× (a , b) true = a

dependentCurry : {A : Set}{B : A → Set}{C : (a : A) → B a → Set} →
  ((a : A)(b : B a) → C a b) ↔ ((w : Σ A B) → C (fst w) (snd w))
fst dependentCurry x (a , b) = x a b
snd dependentCurry x a b = x (a , b)

∀×-distr  : {A : Set}{P : A → Set}{Q : A → Set} → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
fst ∀×-distr x = (λ a → fst (x a)) , λ a → snd (x a)
snd ∀×-distr (f , g) a = f a , g a

Bool=Fin2 : Bool ↔ Fin 2
fst Bool=Fin2 false = zero
fst Bool=Fin2 true = suc zero
snd Bool=Fin2 zero = false
snd Bool=Fin2 (suc x) = true

Fin1+3=Fin4 : Fin (1 + 3) ↔ Fin 1 ⊎ Fin 3
fst Fin1+3=Fin4 zero = inl zero
fst Fin1+3=Fin4 (suc x) = inr x
snd Fin1+3=Fin4 (inl x) = suc (suc (suc x))
snd Fin1+3=Fin4 (inr x) = suc x

-- relating Fin m ⊎ Fin n and Fin (m + n)

inj₁f : {m n : ℕ} → Fin m → Fin (m + n)
inj₁f zero = zero
inj₁f (suc i) = suc (inj₁f i)

test-inj₁f : inj₁f {3}{4} (suc (suc zero)) ≡ suc (suc zero)
test-inj₁f = refl

inj₂f : {m n : ℕ} → Fin n → Fin (m + n)
inj₂f {zero} i = i
inj₂f {suc m} zero = zero
inj₂f {suc m} (suc i) = suc (inj₂f {m} (suc i))

test-inj₂f : inj₂f {3}{4} (suc (suc zero)) ≡ suc (suc (suc (suc (suc zero))))
test-inj₂f = refl

f : {m n : ℕ} → Fin m ⊎ Fin n → Fin (m + n)
f (inl i) = inj₁f i
f (inr i) = inj₂f i

casef : {m n : ℕ}{C : Set} → (Fin m → C) → (Fin n → C) → Fin (m + n) → C
casef {zero} f g i = g i
casef {suc m} f g zero = f zero
casef {suc m} f g (suc i) = casef {m} (λ x → f (suc x)) g i

test-casef : casef {3}{3} (λ i → i) (λ i → i) (suc (suc zero)) ≡ suc (suc zero)
test-casef = refl
test-casef' : casef {3}{3} (λ i → i) (λ i → i) (suc (suc (suc zero))) ≡ zero
test-casef' = refl
test-casef'' : casef {3}{3} (λ i → i) (λ i → i) (suc (suc (suc (suc zero)))) ≡ suc zero
test-casef'' = refl

-- use inj₁f,inj₂f in one direction and "casef inl inr" in the other direction
Fin+ : {m n : ℕ} → Fin (m + n) ↔ Fin m ⊎ Fin n
Fin+ = g , h where
  g : {m n : ℕ} → Fin (m + n) → Fin m ⊎ Fin n
  g x = casef inl inr x

  h : {m n : ℕ} → Fin m ⊎ Fin n → Fin (m + n)
  h (inl x) = inj₁f x
  h (inr x) = inj₂f x

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
 