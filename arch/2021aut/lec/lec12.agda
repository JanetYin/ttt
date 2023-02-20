module 2021aut.lec.lec12 where

open import lib

-- (λ x → t) u = t[x↦u]
-- (λ x → u 3) 4 = (u 3)[x↦4] = u 3
-- NuPRL

-- beszúró rendezés implementációja és helyessége

_≤_ : ℕ → ℕ → Set
zero  ≤ _     = ⊤
suc x ≤ zero  = ⊥
suc x ≤ suc y = x ≤ y

refl≤ : (x : ℕ) → x ≤ x
refl≤ zero    = triv
refl≤ (suc x) = refl≤ x

trans≤ : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
trans≤ zero    _       _       e e' = triv
trans≤ (suc x) (suc y) (suc z) e e' = trans≤ x y z e e'

_<_ : ℕ → ℕ → Set
a < b = suc a ≤ b

≤dec : (x y : ℕ) → (x ≤ y) ⊎ (y < x)
≤dec zero    y = ι₁ triv
≤dec (suc x) zero = ι₂ triv
≤dec (suc x) (suc y) = ≤dec x y

_^_ : Set → ℕ → Set
A ^ zero  = ⊤
A ^ suc n = A × A ^ n

eqℕ : ℕ → ℕ → 𝟚
eqℕ zero zero = tt
eqℕ zero (suc y) = ff
eqℕ (suc x) zero = ff
eqℕ (suc x) (suc y) = eqℕ x y

Eqℕ : ℕ → ℕ → Set
Eqℕ x y = if eqℕ x y then ⊤ else ⊥

-- canvas kvizbol:
f : (ℕ → ℕ) → Set
f = λ x → Eqℕ (x 13) ((λ z → case z (λ (f : 𝟚 → ℕ) → f tt) (λ g → g)) {!!})

Eq^ : (l : ℕ) → ℕ ^ l → ℕ ^ l → Set
Eq^ zero    xs ys = ⊤
Eq^ (suc l) (x , xs) (y , ys) = if eqℕ x y then Eq^ l xs ys else ⊥

exEq^ : {x : ℕ} → Eq^ 3 (1 , x , x , triv) (1 , 2 , 3 , triv)
exEq^ = {!!}

insert : ℕ → (l : ℕ) → ℕ ^ l → ℕ ^ (suc l)
insert y zero    xs       = y , triv
insert y (suc l) (x , xs) = case (≤dec y x)
  (λ _ → y , x , xs)
  (λ _ → x , insert y l xs)

sort : (l : ℕ) → ℕ ^ l → ℕ ^ l
sort zero    xs       = triv
sort (suc l) (x , xs) = insert x l (sort l xs)

Ordered : ℕ → (l : ℕ) → ℕ ^ l → Set
Ordered b zero    xs = ⊤
Ordered b (suc l) (x , xs) = b ≤ x × Ordered x l xs

exOrdered : Ordered 0 3 (1 , 2 , 3 , triv)
exOrdered = _
-- Ordered 0 3 (1 , 2 , 3 , triv) =
-- 0 ≤ 1 × Ordered 1 2 (2 , 3 , triv) = 
-- ⊤ × Ordered 1 2 (2 , 3 , triv) = ...

0-ord : (l : ℕ)(xs : ℕ ^ l)(x : ℕ) → Ordered x l xs → Ordered 0 l xs
0-ord zero    xs x ord = _
0-ord (suc l) (x , xs) y (_ , ord-x-xs) = _ , ord-x-xs

<≤ : (x y : ℕ) → x < y → x ≤ y
<≤ zero y x<y = triv
<≤ (suc x) (suc y) x<y = <≤ x y x<y

lem : (x y : ℕ)(l : ℕ)(xs : ℕ ^ l) → Ordered x l xs → suc x ≤ y →
  x ≤ π₁ (insert y l xs)
lem x y zero xs ord-x-xs x<y = <≤ x y x<y
lem x y (suc l) xs ord-x-xs x<y = ind⊎
  (λ w → x ≤ π₁ (case {A = y ≤ π₁ xs}{π₁ xs < y}{ℕ ^ (suc (suc l))} w (λ _ → y , π₁ xs , π₂ xs)
                        (λ _ → π₁ xs , insert y l (π₂ xs))))
   (λ _ → <≤ x y x<y) (λ _ → π₁ ord-x-xs) (≤dec y (π₁ xs))

ins-ord : (l : ℕ)(xs : ℕ ^ l) → Ordered 0 l xs → (y : ℕ) → 
  Ordered 0 (suc l) (insert y l xs)
ins-ord zero    xs o y = _
ins-ord (suc l) (x , xs) (_ , ord-x-xs) y = ind⊎
  (λ w → Ordered 0 (suc (suc l)) (case w (λ _ → y , x , xs) (λ _ → x , insert y l xs)))
  (λ y≤x → triv , y≤x , ord-x-xs)
  (λ x<y → triv , lem x y l xs ord-x-xs x<y , π₂ (ins-ord l xs (0-ord l xs x ord-x-xs) y))
  (≤dec y x)
{- t : y ≤ x ⊎ x < y
 Ordered 0 (suc (suc l)) (insert y (suc l) (x , xs)) =
 Ordered 0 (suc (suc l)) (case (≤dec y x)
      (λ _ → y , x , xs)
      (λ _ → x , insert y l xs)) =

 (2) Ordered 0 (suc (suc l)) (case (ι₂ x<y)
      (λ _ → y , x , xs)
      (λ _ → x , insert y l xs)) =
 Ordered 0 (suc (suc l)) (x , insert y l xs)

-} 

sort-ord : (l : ℕ)(xs : ℕ ^ l) → Ordered 0 l (sort l xs)
sort-ord zero xs = triv
sort-ord (suc l) (x , xs) =
  ins-ord l (sort l xs) (sort-ord l xs) x
-- Ordered 0 (suc l) (sort (suc l) (x , xs)) =
-- Ordered 0 (suc l) (insert x l (sort l xs))

∈ : ℕ → (l : ℕ) → ℕ ^ l → Set
∈ y zero    xs = ⊥
∈ y (suc l) (x , xs) = Eqℕ x y ⊎ ∈ y l xs

ex∈ : ∈ 3 2 (3 , 3 , triv)
ex∈ = {!!}
