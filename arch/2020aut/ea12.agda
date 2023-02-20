module lec.ea12 where

open import lib

mod3 : ℕ → ℕ
mod3 zero = zero
mod3 (suc zero) = suc zero
mod3 (suc (suc zero)) = suc (suc zero)
mod3 (suc (suc (suc x))) = mod3 x

Eqℕ : ℕ → ℕ → Set
Eqℕ zero zero = ⊤
Eqℕ zero (suc b) = ⊥
Eqℕ (suc a) zero = ⊥
Eqℕ (suc a) (suc b) = Eqℕ a b

Eq3 : ℕ → ℕ → Set
Eq3 x y = Eqℕ (mod3 x) (mod3 y)

f1 : ¬ ((P : ℕ → Set)(x y : ℕ) → Eq3 x y → P x → P y)
f1 = λ w → w (Eqℕ 5) 5 2 tt tt

f2 : (P Q : ℕ → Set)(x y : ℕ) → Eq ℕ x y → (P x → Q x) → (P y → Q y)
f2 P Q x .x refl f = f

-- Eq eliminatora:
transportℕ : (P : ℕ → Set){x y : ℕ} → Eqℕ x y → P x → P y
transportℕ P {zero}  {zero}  e u = u
transportℕ P {suc x} {suc y} e u = transportℕ (λ n → P (suc n)) {x}{y} e u
                                          -- (P ∘ suc)
-- homotopy type theory

-- Eq elimination principle
transport : {A : Set}(P : A → Set){x y : A} → Eq A x y → P x → P y
transport P refl u = u

f2' : (P Q : ℕ → Set)(x y : ℕ) → Eq ℕ x y → (P x → Q x) → (P y → Q y)
f2' = λ P Q _ _ → transport (λ z → P z → Q z)

-----------------------------------------------------------------------------

_^_ : Set → ℕ → Set
A ^ zero  = ⊤
A ^ suc n = A × A ^ n

pl : ℕ ^ 3            -- [ℕ] = List ℕ
pl = 2 , 3 , 1 , tt   -- [2,3,1]

head : {A : Set}{n : ℕ} → A ^ suc n → A
head = proj₁

tail : {A : Set}{n : ℕ} → A ^ suc n → A ^ n
tail = proj₂

_≤_ : ℕ → ℕ → Set
zero  ≤ y     = ⊤
suc x ≤ zero  = ⊥
suc x ≤ suc y = x ≤ y

p : 3 ≤ 100
p = tt
q : ¬ (3 ≤ 2)
q = λ x → x

-- beszuro rendezes:

Dec : Set → Set
Dec A = A ⊎ ¬ A   -- lem : (A : Set) → Dec A

≤dec : (x y : ℕ) → x ≤ y ⊎ y ≤ x  -- alul van specifikalva
≤dec zero    y = inj₁ tt
≤dec (suc x) zero = inj₂ tt
≤dec (suc x) (suc y) = ≤dec x y

insert : ℕ → {n : ℕ} → ℕ ^ n → ℕ ^ (suc n)
insert y {zero}  _  = y , tt
insert y {suc n} (x , xs) = case (≤dec y x)
  (λ _ → y , x , xs)           -- ha y ≤ x
  λ _ → x , insert y {n} xs    -- ha y ≥ x

insert-test1 :
  Eq (ℕ ^ 5) (insert 3 (1 , 2 , 4 , 5 , tt)) (1 , 2 , 3 , 4 , 5 , tt)
insert-test1 = refl

insert-test2 :
  Eq (ℕ ^ 5) (insert 0 (1 , 2 , 4 , 5 , tt)) (0 , 1 , 2 , 4 , 5 , tt)
insert-test2 = refl

sort : {n : ℕ} → ℕ ^ n → ℕ ^ n
sort {zero}  _  = tt
sort {suc n} (x , xs) = insert x (sort {n} xs)

sort-test5 :
  Eq (ℕ ^ 5) (sort (3 , 2 , 1 , 5 , 4 , tt)) (1 , 2 , 3 , 4 , 5 , tt)
sort-test5 = refl

-- garanciák: unit tesztek lefutnak (típusellenőrzés közben), sort terminál,
-- sort n hosszú listából n hosszú listát ad

-- ujOrdered y xs = regiOrdered (y , xs)
Ordered : ℕ → {n : ℕ} → ℕ ^ n → Set
Ordered y {zero}  tt       = ⊤
Ordered y {suc n} (x , xs) = y ≤ x × Ordered x xs
-- Ordered y {n} xs = recℕ ⊤ (λ ...) n

ord-test1 : Ordered 0 {4} (4 , 6 , 9 , 10 , tt)
ord-test1 = tt , tt , tt , tt , tt

ord-test2 : ¬ Ordered 0 {2} (6 , 5 , tt)
ord-test2 = λ w → proj₁ (proj₂ w)

sort-ord : (n : ℕ)(xs : ℕ ^ n) → Ordered 0 (sort xs)
sort-ord n = {!n!}
