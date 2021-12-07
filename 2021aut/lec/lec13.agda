module 2021aut.lec.lec13 where

open import lib

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

0-ord : (l : ℕ)(xs : ℕ ^ l)(x : ℕ) → Ordered x l xs → Ordered 0 l xs
0-ord zero    xs x ord = _
0-ord (suc l) (x , xs) y (_ , ord-x-xs) = _ , ord-x-xs

<≤ : (x y : ℕ) → x < y → x ≤ y
<≤ zero y x<y = triv
<≤ (suc x) (suc y) x<y = <≤ x y x<y

lemma : (x y : ℕ)(l : ℕ)(xs : ℕ ^ l) → Ordered x l xs → suc x ≤ y →
  x ≤ π₁ (insert y l xs)
lemma x y zero xs ord-x-xs x<y = <≤ x y x<y
lemma x y (suc l) xs ord-x-xs x<y = ind⊎
  (λ w → x ≤ π₁ (case {A = y ≤ π₁ xs}{π₁ xs < y}{ℕ ^ (suc (suc l))} w (λ _ → y , π₁ xs , π₂ xs)
                        (λ _ → π₁ xs , insert y l (π₂ xs))))
   (λ _ → <≤ x y x<y) (λ _ → π₁ ord-x-xs) (≤dec y (π₁ xs))

ins-ord : (l : ℕ)(xs : ℕ ^ l) → Ordered 0 l xs → (y : ℕ) → 
  Ordered 0 (suc l) (insert y l xs)
ins-ord zero    xs o y = _
ins-ord (suc l) (x , xs) (_ , ord-x-xs) y = ind⊎
  (λ w → Ordered 0 (suc (suc l)) (case w (λ _ → y , x , xs) (λ _ → x , insert y l xs)))
  (λ y≤x → triv , y≤x , ord-x-xs)
  (λ x<y → triv , lemma x y l xs ord-x-xs x<y , π₂ (ins-ord l xs (0-ord l xs x ord-x-xs) y))
  (≤dec y x)

sort-ord : (l : ℕ)(xs : ℕ ^ l) → Ordered 0 l (sort l xs)
sort-ord zero xs = triv
sort-ord (suc l) (x , xs) =
  ins-ord l (sort l xs) (sort-ord l xs) x

∈ : ℕ → (l : ℕ) → ℕ ^ l → Set
∈ y zero    xs = ⊥
∈ y (suc l) (x , xs) = Eqℕ x y ⊎ ∈ y l xs

ex∈ : ∈ 3 2 (3 , 3 , triv)
ex∈ = {!!}

ex∈' : ∈ 3 2 (3 , 3 , triv)
ex∈' = {!!}

refl= : (n : ℕ) → Eqℕ n n
refl= = {!!}

transport : (P : ℕ → Set)(a b : ℕ) → Eqℕ a b → P a → P b
transport = {!!}

ins-∈ : (y : ℕ)(l : ℕ)(xs : ℕ ^ l) → ∈ y (suc l) (insert y l xs)
ins-∈ = {!!}

ins-other : (y z l : ℕ)(xs : ℕ ^ l) → ∈ y l xs → ∈ y (suc l) (insert z l xs)
ins-other = {!!}

sort-∈ : (y : ℕ)(l : ℕ)(xs : ℕ ^ l) → ∈ y l xs → ∈ y l (sort l xs)
sort-∈ = {!!}
