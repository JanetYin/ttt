open import Lib
open import Lib.Containers.List
open import Lib.Containers.Vector

module lec05 where

module canvas_quiz where

  data A : Set where
    con1 : A → A → A

  a : A
  a = con1 (con1 {!!} {!!}) (con1 {!!} {!!})

  data D : Set where
    con6 : (⊥ → D) → D   -- ∣⊥ → D∣ = ∣D∣^∣⊥∣ = ∣D∣^0 = 1
                         -- ⊤ → D = D^1 = D
 -- con6 : ⊤ → D
 -- con6 : D

  d : D
  d = con6 (λ ())

  data F : Set where
    con8 : F
    con9 : (Bool → F) → F

 {-
   /\
    /\
   /\ 
 -}

  f : F
  f = con9 λ b → if b then con8 else con9 λ b → if b then con9 (λ _ → con8) else con8

  -- eq' : (λ x → 0 + x) ≡ (λ x → x + 0)
  -- eq' = refl

  -- any two f g : A → ⊤,  f = g
  -- η for functions: given f : A → B, f = (λ x → f x)
  -- η for ⊤: given t : ⊤, t = tt
  --------------------------------------------------------------------------------
  -- f =(η for →) λ x → f x =(η for ⊤)  λ x → tt =(η for ⊤) λ x → g x =(η for →) g

  test : (A : Set)(f g : A → ⊤) → f ≡ g
  test A f g = refl

-- DEPENDENT TYPES: Agda, Coq, Lean, Idris, F*

zeroes-l : (n : ℕ) → List ℕ
zeroes-l zero = []
zeroes-l (suc n) = 0 ∷ zeroes-l n

zeroes-v : (n : ℕ) → Vec ℕ n   -- first dependently typed function
zeroes-v zero = []
zeroes-v (suc n) = 0 ∷ zeroes-v n

-- List<A> appendl(List<A> xs, List<A> ys)
append-l : {A : Set} → List A → List A → List A   -- polymorphism is a special case of dependent type
append-l [] ys = ys
append-l (x ∷ xs) ys = x ∷ append-l xs ys

append-v' : (A : Set)(n : ℕ)(m : ℕ) → Vec A n → Vec A m → Vec A (n + m)
append-v' A zero    m []       ys = ys
append-v' A (suc n) m (x ∷ xs) ys = x ∷ append-v' A n m xs ys

append-v : {A : Set}{n : ℕ}{m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
append-v [] ys = ys
append-v (x ∷ xs) ys = x ∷ append-v xs ys

weird-append-v'' : {A : Set}{n : ℕ}{m : ℕ} → Vec A n → Vec A m → Vec A (m + n)
weird-append-v'' xs [] = xs
weird-append-v'' xs (x ∷ ys) = x ∷ weird-append-v'' xs ys

_!!-l_ : {A : Set} → List A → ℕ → Maybe A
[] !!-l n = nothing
(x ∷ xs) !!-l zero = just x
(x ∷ xs) !!-l suc n = xs !!-l n

head-l : {A : Set} → List A → Maybe A
head-l [] = nothing
head-l (x ∷ xs) = just x

head-v : {A : Set}{n : ℕ} → Vec A (suc n) → A
head-v (x ∷ xs) = x

_!!-v_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A
(x ∷ xs) !!-v fzero = x
(x ∷ xs) !!-v fsuc i = xs !!-v i
{-
data List (A : Set) : Set where
  []  : List A
  _∷_ :           A → List A  → List A

data Vec (A : Set) : ℕ → Set where   -- Vec A 0 : Set,  Vec A 1 : Set, Vec A 2 : Set, ...
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

Vec Bool 0 = { [] }
Vec Bool 1 = { true ∷ [] , false ∷ [] }
Vec Bool 2 = { true ∷ true ∷ [] , true ∷ false ∷ [] , false ∷ true ∷ [] , false ∷ false ∷ [] }
..

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc  : {n : ℕ} → Fin n → Fin (suc n)

Fin 0 = {}
Fin 1 = { fzero{0} }
Fin 2 = { fzero{1}, fsuc(fzero{0}) }
Fin 3 = { fzero{2}, fsuc(fzero{1}), fsuc(fsuc(fzero{0})) }
Fin 4 = { fzero{3}, fsuc(fzero{2}), fsuc(fsuc(fzero{1})), fsuc(fsuc(fsuc(fzero{0}))) }
...

A : Set   B : Set      A : Set     B : A → Set          ℕ : Set    Vec Bool : ℕ → Set
-----------------      -----------------------          -----------------------------
 A → B : Set             (x : A) → B x : Set             (n : ℕ) → Vec Bool n : Set

f : A → B   a : A      f : (x : A) → B x     a : A      f : (n:ℕ)→Vec Bool n    3 : ℕ
-----------------      ---------------------------      -----------------------------
    f a : B                     f a : B a                      f 3 : Vec Bool 3

 x : A ⊢ b : B            x : A ⊢ b : B x               n:ℕ ⊢ zero-v n : Vec ℕ n
---------------        -----------------------          ----------------------------------
λ x → b : A → B        λ x → b : (x : A) → B x          λ n → zero-v n : (n : ℕ) → Vec ℕ n

β : (λ x → t) a = t[x↦a]   ,   η : for any f : (x : A) → B x,  f = λ x → f x

-}

-- this class was 3 minutes shorter

