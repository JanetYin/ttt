module 2021aut.lec.lec11 where

open import lib

-- vizsgak keddenkent 9-12 kozott
-- dec14,dec21

{-  f
P x -> Q y              P y -> Q x
 ^      |
 |(1)   |(2)
 |      v
P y    Q x

(1) transport P y x (sym x y e)
(2) transport Q y x (sym x y e)

-}

module canvasKviz where

  open import 2021aut.lec.lec10

  fff : (P Q : ℕ → Set)(x y : ℕ) → Eqℕ x y → (P x → Q y) → (P y → Q x)
  fff P Q x y e f u =
    transportℕ Q y x (sym x y e) (f (transportℕ P y x (sym x y e) u))

-- ha van egy ℕ, akkor indℕ-el lehet mindent bizonyitani rola
-- ha van egy Eqℕ, akkor transportℕ-el tudunk errol mindent belatni

-- x^2+(2*x*y+y^2) =    ... = (x+y)*x + (x+y)*y = (x+y)*(x+y) = (x+y)^2

-- beszúró rendezés implementációja és helyessége

_≤_ : ℕ → ℕ → Set
zero  ≤ _     = ⊤
suc x ≤ zero  = ⊥
suc x ≤ suc y = x ≤ y

pl : 4 ≤ 1000000 -- = suc (suc (suc (suc zero))) ≤ suc (suc (suc (suc 996))) =
              --   zero ≤ 996 = ⊤
pl = triv

refl≤ : (x : ℕ) → x ≤ x
-- refl≤ = indℕ (λ x → x ≤ x) triv (λ n e → e)
refl≤ zero    = triv
refl≤ (suc x) = refl≤ x

trans≤' : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
trans≤' = indℕ (λ x → (y z : ℕ) → x ≤ y → y ≤ z → x ≤ z)
  (λ _ _ _ _ → triv)
  (λ x _ y z e e' →  indℕ (λ y → (z : ℕ) → suc x ≤ y → y ≤ z → suc x ≤ z)
    (λ _ → exfalso)
    (λ y _ z e e' → indℕ (λ z → suc y ≤ z → suc x ≤ z)
      exfalso
      (λ z ih e → {!!})
      z e')
    y z e e')

trans≤ : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
trans≤ zero    _       _       e e' = triv
trans≤ (suc x) (suc y) (suc z) e e' = trans≤ x y z e e'

_≤?_ : ℕ → ℕ → 𝟚
zero  ≤? _     = tt
suc x ≤? zero  = ff
suc x ≤? suc y = x ≤? y

≤dec : (x y : ℕ) → (x ≤ y) ⊎ (y ≤ x)
≤dec zero    y = ι₁ triv
≤dec (suc x) zero = ι₂ triv
≤dec (suc x) (suc y) = ≤dec x y

module example where
  open import 2021aut.lec.lec10 using (Eqℕ)

  =dec : (x y : ℕ) → (Eqℕ x y) ⊎ (¬ Eqℕ x y)
  =dec zero    zero    = ι₁ triv
  =dec zero    (suc y) = ι₂ λ b → b
  =dec (suc x) zero    = ι₂ λ b → b
  =dec (suc x) (suc y) = =dec x y

-- eldontheto tipus:
Dec : Set → Set
Dec A = A ⊎ ¬ A

-- klasszikus logika = minden tipus eldontheto
-- nem lehet irni programot ennek eldontesere:
-- noProgram : (f : ℕ → ℕ) → Dec ((n : ℕ) → Eqℕ (f n) 0)
-- noProgram f = {!f 0!}

---------------------------------------------------------------------------

-- rekurzivan megadott vektorok
_^_ : Set → ℕ → Set
A ^ zero  = ⊤
A ^ suc n = A × A ^ n

-- induktivan megadott vektor
data Vec (A : Set) : ℕ → Set where
  nil : Vec A zero
  cons : A → {n : ℕ} → Vec A n → Vec A (suc n)

head : ∀{A}{n : ℕ}(xs : Vec A (suc n)) → A
head (cons x xs) = x

-- Vec A (suc zero) ≅ A × ⊤
-- A    ^ suc zero  = A × ⊤

countBackFrom : (n : ℕ) → ℕ ^ n
countBackFrom zero    = triv
countBackFrom (suc n) = n , countBackFrom n

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
                             -- Eqℕ x y × Eq^ l xs ys

test-count : Eq^ 3 (countBackFrom 3) (2 , 1 , 0 , triv)
test-count = triv

insert : ℕ → (l : ℕ) → ℕ ^ l → ℕ ^ (suc l)
insert y zero    xs       = y , triv
insert y (suc l) (x , xs) = case (≤dec y x)
  (λ _ → y , x , xs)
  λ _ → x , insert y l xs

-- insert 3 4 (1 , 2 , 4 , 5 , triv) = (1 , 2 , 3 , 4 , 5 , triv)

sort : (l : ℕ) → ℕ ^ l → ℕ ^ l
sort zero    xs       = triv
sort (suc l) (x , xs) = insert x l (sort l xs)

-- unit test
test-sort : Eq^ 5 (sort 5 (3 , 1 , 2 , 6 , 0 , triv)) (0 , 1 , 2 , 3 , 6 , triv)
test-sort = triv

module twoProducts where

  data _×ind_ (A B : Set) : Set where
    _,_ : A → B → A ×ind B

  π₁' : ∀{A B} → A ×ind B → A
  π₁' (a , b) = a
  π₂' : ∀{A B} → A ×ind B → B
  π₂' (a , b) = b

  record _×rec_ (A B : Set) : Set where
    constructor _,_
    field
      π₁ : A
      π₂ : B
  open _×rec_

  ηrec : {A B : Set}(w : A ×rec B) → Eq (A ×rec B) w (π₁ w , π₂ w)
  ηrec w = refl

  ηind : {A B : Set}(w : A ×ind B) → Eq (A ×ind B) w (π₁' w , π₂' w)
  ηind (a , b) = refl

  -- induktiv tipusok, koinduktiv tipusok, univerzum(Set)
  -- Σ               , Π
