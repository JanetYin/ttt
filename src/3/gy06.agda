open import lib

data Fin : ℕ → Set where  -- Fin n = n-elemu halmaz
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)


Σ=⊎ : {A B : Set} → Σ Bool (if_then A else B) ↔ A ⊎ B
fst Σ=⊎ (false , avb) = inr avb
fst Σ=⊎ (true , avb) = inl avb
snd Σ=⊎ (inl x) = true , x
snd Σ=⊎ (inr x) = false , x

Σ=× : {A B : Set} → Σ A (λ _ → B) ↔ A × B
Σ=× = (λ where (a , b) → a , b) , λ where (a , b) → a , b

Π=→ : {A B : Set} → ((a : A) → (λ _ → B) a) ≡ (A → B)
Π=→ = refl

→=× : {A B : Set} → ((b : Bool) → if b then A else B) ↔ A × B
fst →=× = λ x → x true , x false
snd →=× = λ where (x , y) false → y
                  (x , y) true → x

dependentCurry : {A : Set}{B : A → Set}{C : (a : A) → B a → Set} →
  ((a : A)(b : B a) → C a b) ↔ ((w : Σ A B) → C (fst w) (snd w))
dependentCurry = (λ where x (a , ba) → x a ba) , λ x a b → x (a , b)

∀×-distr  : {A : Set}{P : A → Set}{Q : A → Set} → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
∀×-distr = (λ x → (λ a → fst (x a)) , λ a → snd (x a)) , (λ (p , q) a → p a , q a)

Bool=Fin2 : Bool ↔ Fin 2
fst Bool=Fin2 false = zero
fst Bool=Fin2 true = suc zero
snd Bool=Fin2 zero = false
snd Bool=Fin2 (suc x) = true

Fin1+3=Fin4 : Fin (1 + 3) ↔ Fin 1 ⊎ Fin 3
fst Fin1+3=Fin4 zero = inl zero
fst Fin1+3=Fin4 (suc x) = inr x
snd Fin1+3=Fin4 (inl zero) = zero
snd Fin1+3=Fin4 (inr x) = suc x

-- relating Fin m ⊎ Fin n and Fin (m + n)

inj₁f : {m n : ℕ} → Fin m → Fin (m + n)
inj₁f zero = zero
inj₁f (suc i) = suc (inj₁f i)

test-inj₁f : inj₁f {3}{4} (suc (suc zero)) ≡ suc (suc zero)
test-inj₁f = refl

inj₂f : {m n : ℕ} → Fin n → Fin (m + n)
inj₂f {zero} {n} i = i
inj₂f {suc m} {suc n} zero = zero
inj₂f {suc m} {suc n} (suc i) = suc (inj₂f {m} {suc n} (suc i))

test-inj₂f : inj₂f {3}{4} (suc (suc zero)) ≡ suc (suc (suc (suc (suc zero))))
test-inj₂f = refl

f : {m n : ℕ} → Fin m ⊎ Fin n → Fin (m + n)
f (inl i) = inj₁f i
f (inr i) = inj₂f i

casef : {m n : ℕ}{C : Set} → (Fin m → C) → (Fin n → C) → Fin (m + n) → C
casef {zero} {n} {C} f g i = g i
casef {suc m} {n} {C} f g zero = f zero
casef {suc m} {n} {C} f g (suc i) = casef {m} {n} {C} (λ x → f (suc x)) g i

test-casef : casef {3}{3} (λ i → i) (λ i → i) (suc (suc zero)) ≡ suc (suc zero)
test-casef = refl
test-casef' : casef {3}{3} (λ i → i) (λ i → i) (suc (suc (suc zero))) ≡ zero
test-casef' = refl
test-casef'' : casef {3}{3} (λ i → i) (λ i → i) (suc (suc (suc (suc zero)))) ≡ suc zero
test-casef'' = refl

-- use inj₁f,inj₂f in one direction and "casef inl inr" in the other direction
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
