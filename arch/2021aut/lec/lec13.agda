module 2021aut.lec.lec13 where

open import lib

eqℕ : ℕ → ℕ → 𝟚
eqℕ zero zero = tt
eqℕ zero (suc y) = ff
eqℕ (suc x) zero = ff
eqℕ (suc x) (suc y) = eqℕ x y

Eqℕ : ℕ → ℕ → Set
Eqℕ x y = if eqℕ x y then ⊤ else ⊥

transport : (P : ℕ → Set)(a b : ℕ) → Eqℕ a b → P a → P b
transport P zero    zero    e u = u
transport P (suc a) (suc b) e u = transport (λ x → P (suc x)) a b e u

refl= : (n : ℕ) → Eqℕ n n
refl= = indℕ (λ n → Eqℕ n n) triv λ _ e → e

cong : (f : ℕ → ℕ) (x y : ℕ) → Eqℕ x y → Eqℕ (f x) (f y)
cong f x y e = transport (λ y → Eqℕ (f x) (f y)) x y e (refl= (f x))

module kviz where
  mod3 : ℕ → ℕ
  mod3 zero = zero
  mod3 (suc zero) = suc zero
  mod3 (suc (suc zero)) = suc (suc zero)
  mod3 (suc (suc (suc x))) = mod3 x

  Eq3 : ℕ → ℕ → Set
  Eq3 x y = Eqℕ (mod3 x) (mod3 y)

  a : (P : ℕ → Set)(x y : ℕ) → Eq3 x y → P (mod3 x) → P (mod3 y)
  a P x y = transport P (mod3 x) (mod3 y)
  b : ¬ ((x y : ℕ) → Eq3 x y → Eqℕ x y)
  b = λ w → w 0 3 triv
  c : ¬ ((P : ℕ → Set)(x y : ℕ) → Eq3 x y → P x → P y)
  c = λ w → w (Eqℕ 0) 0 3 triv triv
  d : (x y : ℕ) → Eqℕ x y → Eq3 x y
  d = cong mod3
  -- e    : Eqℕ x        y
  -- kell : Eqℕ (mod3 x) (mod3 y)

  e : ¬ ((R : ℕ → ℕ → Set) → (R zero zero → R (suc zero) (suc zero)))
  e = λ w → w R triv
    where
      R : ℕ → ℕ → Set
      R zero zero = ⊤
      R (suc _) _ = ⊥
      R zero (suc _) = ⊥

  f : ¬ ((R : ℕ → ℕ → Set) → (Σ ℕ (λ x → Σ ℕ (λ y → R x y)) → Σ ℕ (λ x → R x x)))
  f w = g (π₁ (w R (0 , 1 , triv))) (π₂ (w R (0 , 1 , triv))) 
    where
      R : ℕ → ℕ → Set
      R zero (suc zero) = ⊤
      R _ _ = ⊥

      g : (x : ℕ) → ¬ R x x
      g = indℕ (λ x → ¬ R x x) (λ b → b) (λ _ _ b → b)

  g : (R : ℕ → ℕ → Set) → Σ ℕ (λ x → R x x) → (Σ ℕ (λ x → Σ ℕ (λ y → R x y)))
  g R (x , Rxx) = x , x , Rxx

  h : (R : ℕ → ℕ → Set) → Σ (ℕ × ℕ) (λ w → R (π₁ w) (π₂ w)) → (Σ ℕ (λ x → Σ ℕ (λ y → R x y)))
  h R ((x , y) , Rxy) = x , y , Rxy

  h⁻¹ : (R : ℕ → ℕ → Set) → (Σ ℕ (λ x → Σ ℕ (λ y → R x y)) → Σ (ℕ × ℕ) (λ w → R (π₁ w) (π₂ w)))
  h⁻¹ R (x , y , Rxy) = (x , y) , Rxy

  -- (A×B)×C ≅ A×(B×C)
  assΣ1 : ∀{A : Set}{B : A → Set}{C : (a : A) → B a → Set} →
    Σ A (λ a → Σ (B a) λ b → C a b) → Σ (Σ A B) λ ab → C (π₁ ab) (π₂ ab)
  assΣ1 (a , (b , c)) = ((a , b) , c)

  -- ∀A,B f : A⊎B → B⊎A, g : B⊎A→A⊎B,   fg : minden ba:B⊎A-ra   f (g ba) = ba,         Eqℕ (suc x) (suc y) = Eqℕ x y,    Eq ℕ (suc x) (suc y) ≠ Eq ℕ x y
  -- Eq (mod3 (suc x)) (mod3 (suc y)) → Eq (mod3 x) (mod3 y)
  -- mod3 (suc x) = suc (mod3 x)

  record _≅_ (A B : Set) : Set where
    field
      ab : A → B
      ba : B → A
      bb : (b : B) → Eq B (ab (ba b)) b
      aa : (a : A) → Eq A (ba (ab a)) a
  open _≅_

  nem : ¬ ((A B : Set) → A ≅ B)
  nem = {!!}

  assΣ : ∀{A : Set}{B : A → Set}{C : (a : A) → B a → Set} →
    Σ A (λ a → Σ (B a) λ b → C a b) ≅ Σ (Σ A B) λ ab → C (π₁ ab) (π₂ ab)
  ab assΣ (a , (b , c)) = ((a , b) , c)
  ba assΣ ((a , b) , c) = (a , (b , c))
  bb assΣ ((a , b) , c) = refl
  aa assΣ (a , (b , c)) = refl

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
∈ y (suc l) (x , xs) =
  Eqℕ x y ⊎ ∈ y l xs

ex∈ : ∈ 3 2 (3 , 3 , triv)
ex∈ = ι₁ triv

ex∈' : ∈ 3 2 (3 , 3 , triv)
ex∈' = ι₂ (ι₁ triv)

ins-∈ : (y : ℕ)(l : ℕ)(xs : ℕ ^ l) → ∈ y (suc l) (insert y l xs)
ins-∈ y zero    xs = ι₁ (refl= y)
ins-∈ y (suc l) (x , xs) = ind⊎ (λ w → ∈ y (suc (suc l)) (case w (λ _ → y , x , xs) (λ _ → x , insert y l xs)))
  (λ y≤x → ι₁ (refl= y))
  (λ x<y → ι₂ (ins-∈ y l xs))
  (≤dec y x)
-- ∈ y (suc (suc l)) (insert y (suc l) (x, xs)) =
-- ∈ y (suc (suc l)) (case (≤dec y x) (λ _ → y , x , xs) (λ _ → x , insert y l xs))

ins-other : (y z l : ℕ)(xs : ℕ ^ l) → ∈ y l xs → ∈ y (suc l) (insert z l xs)
ins-other y z (suc l) (x , xs) y∈x,xs = ind⊎ (λ w → ∈ y (suc (suc l)) (case w (λ _ → z , x , xs) (λ _ → x , insert z l xs)))
  (λ z≤x → ι₂ y∈x,xs)
  (λ x<z → case y∈x,xs ι₁ λ y∈xs → ι₂ (ins-other y z l xs y∈xs))
  (≤dec z x)
-- ∈ y (suc (suc l)) (insert z (suc l) (x , xs)) =
-- ∈ y (suc (suc l)) (case (≤dec z x) (λ _ → z , x , xs) (λ _ → x , insert z l xs))

sort-∈ : (y : ℕ)(l : ℕ)(xs : ℕ ^ l) → ∈ y l xs → ∈ y l (sort l xs)
sort-∈ y (suc l) (x , xs) (ι₁ x=y) = transport (λ y → ∈ y (suc l) (sort (suc l) (x , xs))) x y x=y (ins-∈ x l (sort l xs)) 
-- sort (suc l) (x , xs) = insert x l (sort l xs)
sort-∈ y (suc l) (x , xs) (ι₂ y∈xs) = ins-other y x l (sort l xs) (sort-∈ y l xs y∈xs)
-- Eqℕ x y ⊎ ∈ y l xs
-- Eqℕ (π₁ (insert x l (sort l xs))) y ⊎ ∈ y l (π₂ (insert x l (sort l xs)))
-- ∈ y (suc l) (sort (suc l) (x , xs)) = 
-- ∈ y (suc l) (insert x l (sort l xs))
