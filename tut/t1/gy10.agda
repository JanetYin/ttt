module tut.t1.gy10 where

open import lib

not : Bool → Bool
not true = false
not false = true

---------------------------------------------------------
-- First order logic
---------------------------------------------------------

∀×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
∀⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → ((a : A) → P a ⊎ Q a)  ← ((a : A) → P a) ⊎ ((a : A) → Q a)
Σ×-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a × Q a)  → Σ A P × Σ A Q
Σ⊎-distr  :    (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a)  ↔ Σ A P ⊎ Σ A Q
¬∀        :    (A : Set)(P : A → Set)              → (Σ A λ a → ¬ P a)      → ¬ ((a : A) → P a)
¬Σ        :    (A : Set)(P : A → Set)              → (¬ Σ A λ a → P a)      ↔ ((a : A) → ¬ P a)
⊎↔ΣBool   :    (A B : Set)                         → (A ⊎ B)                ↔ Σ Bool (λ b → if b then A else B)
¬¬∀-nat   :    (A : Set)(P : A → Set)              → ¬ ¬ ((x : A) → P x)    → (x : A) → ¬ ¬ (P x)

-- ∀a(P(a) ∧ Q(a)) ↔ ∀aP(a) ∧ ∀aQ(a)
∀×-distr A P Q = (λ t → (λ a → proj₁ (t a)) , λ a → proj₂ (t a))
               , λ t a → proj₁ t a , proj₂ t a 

∀⊎-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → (((a : A) → P a ⊎ Q a) → ((a : A) → P a) ⊎ ((a : A) → Q a)))
∀⊎-distr' t = {!!}
  where

Σ×-distr' : ¬ ((A : Set)(P : A → Set)(Q : A → Set) → ((Σ A λ a → P a × Q a) ← Σ A P × Σ A Q))
Σ×-distr' t = {!!}

Σ∀       : (A B : Set)(R : A → B → Set)        → (Σ A λ x → (y : B) → R x y) → (y : B) → Σ A λ x → R x y
AC       : (A B : Set)(R : A → B → Set)        → ((x : A) → Σ B λ y → R x y) → Σ (A → B) λ f → (x : A) → R x (f x)

---------------------------------------------------------
-- Vectors
---------------------------------------------------------

_^_ : Set → ℕ → Set
A ^ zero  = ⊤
A ^ suc x = A × A ^ x

exVec : Bool ^ 3
exVec = false , true , true , tt

nil : {A : Set} → A ^ 0
nil = tt

cons : {A : Set}{n : ℕ} → A → A ^ n → A ^ (suc n)
cons = _,_

head : {A : Set}{n : ℕ} → A ^ (suc n) → A
head = proj₁

tail : {A : Set}{n : ℕ} → A ^ (suc n) → A ^ n
tail = proj₂

⊤s : (n : ℕ) → ⊤ ^ n
⊤s = λ n → indℕ (⊤ ^_) tt (λ n tts → tt , tts) n

-- ezt nem kell kiadni feladatnak:
_+_ : ℕ → ℕ → ℕ
zero + b = b 
suc a + b = suc (a + b)

_++_ : {A : Set}{n m : ℕ} → A ^ n → A ^ m → A ^ (n + m)
_++_ = {!!}

isEven = rec true not

filter[_] : {A : Set}(n : ℕ)(f : A → Bool) → A ^ n → Σ ℕ λ m → A ^ m
filter[_] = {!!}

-- ezt nem kell kiadni feladatnak:
_≤_ : ℕ → ℕ → Set
zero  ≤ y     = ⊤
suc x ≤ zero  = ⊥
suc x ≤ suc y = x ≤ y

_<_ : ℕ → ℕ → Set
a < b = suc a ≤ b

-- n-edik elem
!! : {A : Set} (n : ℕ) → A ^ n → (m : ℕ) → m < n → A
!! (suc n) (x , xs) zero e = x
!! (suc n) (x , xs) (suc m) e = !! n xs m e

eqn : ℕ → ℕ → Bool
eqn zero zero = true
eqn zero (suc m) = false
eqn (suc n) zero = false
eqn (suc n) (suc m) = eqn n m

-- inj₂-t ad vissza, ha xs-ben nincs benne x
lookup'' : (n : ℕ)(x : ℕ)(xs : ℕ ^ n) → ℕ ⊎ ⊤
lookup'' = {!!}
  
Decidable : Set → Set
Decidable = λ A → A ⊎ ¬ A

lookup : (n : ℕ)(x : ℕ)(xs : ℕ ^ n) → Decidable (Σ ℕ λ i → Σ (i < n) λ p → Eq ℕ (!! n xs i p) x)
lookup zero x xs = inj₂ λ t → {!!}
lookup (suc n) x xs = {!!}

-- ezt nem kell kiadni feladatnak:
≤dec : (x y : ℕ) → x ≤ y ⊎ y ≤ x
≤dec zero y = inj₁ tt
≤dec (suc x) zero = inj₂ tt
≤dec (suc x) (suc y) = ≤dec x y

-- ez lesz eloadason:
insert : ℕ → {l : ℕ} → ℕ ^ l → ℕ ^ (suc l)
insert y {zero}  xs       = y , tt
insert y {suc l} (x , xs) = case (≤dec y x)
  (λ _ → y , x , xs)
  (λ _ → x , insert y xs)

insert-test1 : Eq (ℕ ^ 5) (insert 3 (1 , 2 , 4 , 5 , tt)) (1 , 2 , 3 , 4 , 5 , tt)
insert-test1 = refl

insert-test2 : Eq (ℕ ^ 5) (insert 0 (1 , 2 , 4 , 5 , tt)) (0 , 1 , 2 , 4 , 5 , tt)
insert-test2 = refl

insert-test3 : Eq (ℕ ^ 5) (insert 1 (1 , 2 , 4 , 5 , tt)) (1 , 1 , 2 , 4 , 5 , tt)
insert-test3 = refl

insert-test4 : Eq (ℕ ^ 5) (insert 10 (1 , 2 , 4 , 5 , tt)) (1 , 2 , 4 , 5 , 10 , tt)
insert-test4 = refl

-- ez lesz eloadason:
sort : {l : ℕ} → ℕ ^ l → ℕ ^ l
sort {zero}   _       = tt
sort {suc l} (x , xs) = insert x (sort xs)

sort-test5 : Eq (ℕ ^ 5) (sort (3 , 2 , 1 , 5 , 4 , tt)) (1 , 2 , 3 , 4 , 5 , tt)
sort-test5 = refl

sort-test6 : Eq (ℕ ^ 5) (sort (2 , 2 , 1 , 4 , 4 , tt)) (1 , 2 , 2 , 4 , 4 , tt)
sort-test6 = refl

-- ezt nem kell kiadni feladatnak:
Ordered : ℕ → (l : ℕ) → ℕ ^ l → Set
Ordered b zero tt          = ⊤
Ordered b (suc l) (x , xs) = b ≤ x × Ordered x l xs

ord-test1 : Ordered 3 4 (4 , 7 , 9 , 10 , tt)
ord-test1 = tt , tt , tt , tt , tt

ord-test1a : Ordered 3 4 (4 , 4 , 9 , 10 , tt)
ord-test1a = tt , tt , tt , tt , tt

ord-test2 : ¬ Ordered 0 2 (2 , 1 , tt)
ord-test2 = λ z → proj₁ (proj₂ z)

ord-test3 : ¬ Ordered 1 2 (0 , 0 , tt)
ord-test3 = proj₁

-- ez lesz eloadason
ins-ord : {l : ℕ}(xs : ℕ ^ l)(b : ℕ) → Ordered b l xs → (y : ℕ) → b ≤ y →
  Ordered b (suc l) (insert y xs)
ins-ord {zero}  xs       b tt               y b≤y = b≤y , tt
ins-ord {suc l} (x , xs) b (b≤x , ord-x-xs) y b≤y = ind⊎
  (λ w → Ordered b (2 + l) (case w (λ _ → y , x , xs) (λ _ → x , insert y xs)))
  (λ y≤x → b≤y , y≤x , ord-x-xs)                -- Ordered b _ (y , x , xs)        = b ≤ y × Ordered y _ (x , xs)        = b ≤ y × y ≤ x × Ordered x _ xs
  (λ x≤y → b≤x , ins-ord xs x ord-x-xs y x≤y) -- Ordered b _ (x , insert y xs) = b ≤ x × Ordered x _ (insert y xs)
  (≤dec y x) 

-- ez lesz eloadason
sort-ord : (l : ℕ)(xs : ℕ ^ l) → Ordered 0 l (sort xs)
sort-ord zero xs = tt
sort-ord (suc l) (x , xs) = ins-ord (sort xs) 0 (sort-ord l xs) x tt

∈ : (y : ℕ)(l : ℕ)(xs : ℕ ^ l) → Set
∈ y zero    tt       = ⊥
∈ y (suc l) (x , xs) = Eq ℕ y x ⊎ ∈ y l xs

∈-test1 : ∈ 3 4 (6 , 4 , 3 , 2 , tt)
∈-test1 = inj₂ (inj₂ (inj₁ refl))

∈-test2a : ∈ 3 4 (6 , 4 , 3 , 3 , tt)
∈-test2a = inj₂ (inj₂ (inj₁ refl))

∈-test2b : ∈ 3 4 (6 , 4 , 3 , 3 , tt)
∈-test2b = inj₂ (inj₂ (inj₂ (inj₁ refl)))

∈-test3 : ¬ ∈ 3 4 (1 , 1 , 1 , 1 , tt)
∈-test3 = {!!}

-- ez lesz eloadason
ins-∈ : (y : ℕ)(l : ℕ)(xs : ℕ ^ l) → ∈ y (suc l) (insert y xs)
ins-∈ y zero xs = inj₁ refl
ins-∈ y (suc l) (x , xs) = ind⊎
  (λ w → ∈ y (suc (suc l)) (case w (λ _ → y , x , xs) (λ _ → x , insert y xs)))
  (λ y≤x → inj₁ refl)
  (λ x≤y → inj₂ (ins-∈ y l xs))
  (≤dec y x)

-- ez lesz eloadason
ins-other : (y z l : ℕ)(xs : ℕ ^ l) → ∈ y l xs → ∈ y (suc l) (insert z xs)
ins-other y z zero _ ()
ins-other y z (suc l) (x , xs) y∈x,xs = ind⊎
  (λ w → ∈ y (suc (suc l)) (case w (λ _ → z , x , xs) (λ _ → x , insert z xs)))
  (λ z≤x → inj₂ y∈x,xs)
  (λ x≤z → case y∈x,xs inj₁ λ y∈xs → inj₂ (ins-other y z l xs y∈xs))
  (≤dec z x)

-- ez lesz eloadason
sort-∈ : (y : ℕ)(l : ℕ)(xs : ℕ ^ l) → ∈ y l xs → ∈ y l (sort xs)
sort-∈ y (suc l) (x , xs) (inj₁ refl) = ins-∈ y l (sort xs)
sort-∈ y (suc l) (x , xs) (inj₂ y∈xs) = ins-other y x l _ (sort-∈ y l xs y∈xs)
