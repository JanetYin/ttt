module lec.ea13 where

open import lib

_+_ : ℕ → ℕ → ℕ
zero + b = b
suc a + b = suc (a + b)

u v : ℕ
u = {!!}
v = {!!}

t : Eq ℕ u v
t = {!!}

sym : {A : Set}{x y : A} → Eq A x y → Eq A y x
sym refl = refl

w : Σ ℕ λ k → Eq ℕ (k + v) u
w = 0 , sym t -- (0 , t)

--------------------------------------------------------

_^_ : Set → ℕ → Set
A ^ zero  = ⊤
A ^ suc x = A × A ^ x

_≤_ : ℕ → ℕ → Set
zero  ≤ y     = ⊤
suc x ≤ zero  = ⊥
suc x ≤ suc y = x ≤ y

_<_ : ℕ → ℕ → Set
a < b = suc a ≤ b

≤dec : (x y : ℕ) → x ≤ y ⊎ y ≤ x
≤dec zero y = inj₁ tt
≤dec (suc x) zero = inj₂ tt
≤dec (suc x) (suc y) = ≤dec x y

insert : ℕ → {n : ℕ} → ℕ ^ n → ℕ ^ (suc n)
insert y {zero}  xs       = y , tt
insert y {suc n} (x , xs) = case (≤dec y x)
  (λ _ → y , x , xs)
  (λ _ → x , insert y xs)

sort : {n : ℕ} → ℕ ^ n → ℕ ^ n
sort {zero}   _       = tt
sort {suc n} (x , xs) = insert x (sort xs)

-- Ordered y xs = (y , xs) lista rendezett
Ordered : ℕ → {n : ℕ} → ℕ ^ n → Set
Ordered y {zero}  tt       = ⊤
Ordered y {suc n} (x , xs) = y ≤ x × Ordered x xs

ord-test1 : Ordered 0 {4} (4 , 6 , 5 , 10 , tt)
-- (0 ≤ 4) × (4 ≤ 6) × (6 ≤ 5) × (5 ≤ 10) × ⊤
ord-test1 = {!!}

ins-ord : {n : ℕ}{xs : ℕ ^ n}{b : ℕ} →
  Ordered b xs → (y : ℕ) → b ≤ y → Ordered b (insert y xs)
ins-ord {zero} {xs} {b} ord-b-xs y b≤y = b≤y , tt
ins-ord {suc n}{x , xs} {b} (b≤x , ord-b-xs) y b≤y = ind⊎
  (λ z → Ordered b {2 + n} (case z (λ _ → y , x , xs) (λ _ → x , insert y xs)))
  (λ y≤x → b≤y , y≤x , ord-b-xs)
  (λ x≤y → b≤x , ins-ord ord-b-xs y x≤y)
                 -- Ordered b (x , insert y xs)
                 -- = b ≤ x × Ordered x (insert y xs)
  (≤dec y x)
-- kell : Ordered b (insert y (x , xs))
--   = Ordered b (case (≤dec y x) (λ _ → y , x , xs) (λ _ → x , insert y xs))

sort-ord : (n : ℕ)(xs : ℕ ^ n) → Ordered 0 (sort xs)
sort-ord zero    xs = tt
sort-ord (suc n) (x , xs) = ins-ord (sort-ord n xs) x tt
-- sort-ord (suc n) (x , xs) : Ordered 0 (insert x (sort xs))
-- sort-ord n xs : Ordered 0 (sort xs)

sort' : {n : ℕ} → ℕ ^ n → ℕ ^ n
sort' {zero} xs = tt
sort' {suc n} (x , xs) = 0 , sort' xs

sort'-ord : (n : ℕ)(xs : ℕ ^ n) → Ordered 0 (sort' xs)
sort'-ord zero xs = tt
sort'-ord (suc n) (x , xs) = tt , sort'-ord n xs
--  Ordered 0 (sort' (x , xs)) =
--  Ordered 0 (0 , sort' xs) =
--  0 ≤ 0 × Ordered 0 (sort' xs)

_∈_ : (y : ℕ){n : ℕ}(xs : ℕ ^ n) → Set
_∈_ y {zero}    tt       = ⊥
_∈_ y {suc n} (x , xs) = Eq ℕ y x ⊎ y ∈ xs

ins-∈ : (y : ℕ)(l : ℕ)(xs : ℕ ^ l) → y ∈ insert y xs
ins-∈ y zero xs = inj₁ refl
ins-∈ y (suc l) (x , xs) = ind⊎
  (λ w → _∈_ y {suc (suc l)} (case w (λ _ → y , x , xs) (λ _ → x , insert y xs)))
  (λ y≤x → inj₁ refl)
  (λ x≤y → inj₂ (ins-∈ y l xs))
  (≤dec y x)

ins-other : (y z l : ℕ)(xs : ℕ ^ l) → y ∈ xs → y ∈ insert z xs
ins-other y z zero _ ()
ins-other y z (suc l) (x , xs) y∈x,xs = ind⊎
  (λ w → _∈_ y {suc (suc l)} (case w (λ _ → z , x , xs) (λ _ → x , insert z xs)))
  (λ z≤x → inj₂ y∈x,xs)
  (λ x≤z → case y∈x,xs inj₁ λ y∈xs → inj₂ (ins-other y z l xs y∈xs))
  (≤dec z x)

sort-∈ : (y : ℕ)(n : ℕ)(xs : ℕ ^ n) → y ∈ xs → y ∈ sort xs
sort-∈ y (suc l) (x , xs) (inj₁ refl) = ins-∈ y l (sort xs)
sort-∈ y (suc l) (x , xs) (inj₂ y∈xs) = ins-other y x l _ (sort-∈ y l xs y∈xs)

-- amit ez nem véd ki: 1,1,0 -> 0,0,1
