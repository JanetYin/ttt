open import Lib hiding (Fin)
open import Lib.Containers.Vector hiding (length; _++_)
open import Lib.Containers.List hiding (length; _++_)

{-
Boolβ₁ : if true then u else v = u
Boolβ₂ : if false then u else v = u
⊤η     : t = tt

-- 2. feladat D,E,F-re mindenki maxpontot kap

(λ x → if x then x else x) ≠ (λ x → x) : Bool → Bool
(λ x → if x then tt else tt) ≠ (λ x → tt) : Bool → ⊤


-}

-- data F : Set where
--   con8 : F
--  con9 : F → F → F       -- (Bool → F) = "F^2" ≅ F × F
--  con9 : (Bool → F) → F       -- (Bool → F) = "F^2" ≅ F × F

-- (λ n → iteℕ n (λ _ → n) n) ≠ (λ n → n)

-- (λ n → iteℕ 42 (λ i → n) n) 0 ≠ 0  csak nem-nulla szamokra az identitas
-- (λ n → iteℕ 42 (λ i → n) 42) = (λ n → iteℕ 42 (λ i → n) (suc 41)) =
--     (λ n → (λ i → n) (iteℕ 42 (λ i → n 41))) = (λ n → n)
-- (λ n → iteℕ n (λ i → 42) zero) = (λ n → n)
-- n = ssssz   |--->  ssssz

module ea06 (A : Set) where

f : A → ⊤
f = _

-- ez az ora 2 perccel rovidebb

--------------------------------------------------------------------
-- fuggo tipusok
--------------------------------------------------------------------

zeroes-l : ℕ → List ℕ
zeroes-l _ = 0 ∷ 0 ∷ []
-- zeroes-l zero    = []
-- zeroes-l (suc n) = 0 ∷ zeroes-l n

zeroes-v : (n : ℕ) → Vec ℕ n      -- a kimenet tipusaban szerepel a bemenet erteke
zeroes-v zero    = []
zeroes-v (suc n) = 0 ∷ zeroes-v n

append-l : {A : Set} → List A → List A → List A
append-l []       ys = ys
append-l (x ∷ xs) ys = x ∷ append-l xs ys

append-v : {A : Set}(m n : ℕ) → Vec A m → Vec A n → Vec A (m + n)
append-v zero    n []       ys = ys
-- [] : Vec A zero
-- ys : Vec A n
-- ys : Vec A n
append-v (suc m') n (x ∷ xs) ys = x ∷ append-v m' n xs ys
-- (x ∷ xs)                : Vec A (suc m')
-- ys                      : Vec A n
-- ?                       : Vec A (suc (m' + n))
-- append-v m' n xs ys     : Vec A (m' + n)
-- x ∷ append-v m' n xs ys : Vec A (suc (m' + n))

length : {A : Set} → List A → ℕ             -- fuggo tipus
length [] = zero
length (_ ∷ xs) = suc (length xs)

-- implicit parameter {}-k kozott
-- infixl _++_ 4 -- ((xs ++ ys) ++ zs)
_++_ : {A : Set}{m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- _→_ : Set → Set → Set

xs : Vec Bool 3
xs = true ∷ false ∷ false ∷ []

ys : Vec Bool 6
ys = _++_ {Bool}{3}{_} xs xs -- expliciten megadtam az osszes parametert

-- _∘_ : {A B C : Set} → (B → C) → (A → B) → A → C

-- List is egy tipuscsalad
-- List : Set → Set
-- List ℕ : Set, List Bool : Set, List (List Bool) : Set, 
-- Vec egy tipuscsalad
-- Vec : Set → ℕ → Set
-- List A : Set,    Vec A 0 : Set,   Vec A 1 : Set,  Vec A 2 : Set, ...
{-
data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : A → {n : ℕ} → Vec A n → Vec A (suc n)
-}

head' : {A : Set} → List A → Maybe A
head' [] = nothing
head' (x ∷ xs₁) = just x

head'' : {A : Set}{n : ℕ} → Vec A (suc n) → A
head'' (x ∷ xs₁) = x

_!!'_ : {A : Set} → List A → ℕ → Maybe A
[]       !!' _     = nothing
(x ∷ xs) !!' zero  = just x
(x ∷ xs) !!' suc n = xs !!' n

data Fin : ℕ → Set where  -- Fin n az n-elemu tipus ,  Fin n = {0,1,2,3,...,n-1}
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)
{-
zero {0} : Fin 1
zero {1} : Fin 2
suc (zero{0}) : Fin 2

Fin 0 =                                                              {}
Fin 1 =                                                  {zero{0}}
Fin 2 =            {                 zero{1},          suc (zero{0})}
Fin 3 =            {zero{2},     suc (zero{1}),     suc(suc (zero{0}))}
Fin 4 = {zero{3},suc(zero{2}),suc(suc (zero{1})),suc(suc(suc (zero{0})))}
...
-}

f01 : Fin 1
f01 = zero

f02 f12 : Fin 2
f02 = zero
f12 = suc zero

f03 f13 f23 : Fin 3
f03 = zero 
f13 = suc zero
f23 = suc (suc zero)

_!!_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A
(x ∷ xs) !! zero  = x
(x ∷ xs) !! suc i = xs !! i

-- Π and Σ

-- Π = fuggo fuggveny tipus  (x : A) → B x       Π(x : A).B x

-- A → B,    λ, applikacio(space), β, η
{-
           Γ,x:A ⊢ t : B                  Γ,A:Set ⊢ t : B
      -------------------------        ---------------------------
      Γ ⊢ λ x → t : (x : A) → B        Γ ⊢ λ A → t : (A : Set) → B

  t : (x : A) → B       u : A
  ---------------------------
     t u : B[x↦u]

  t : (n : ℕ) → Vec ℕ n    3 : ℕ
  ------------------------------
     t 3 : Vec ℕ 3
-}
pluszegy : (x : ℕ) → ℕ
pluszegy x = x + 1

-- fuggo fuggveny tipus altalanositja a →-t

-- _×_ altalanositasa: Σ
{-
record Σ (A : Set)(B : A → Set) : Set where
  field
    fst : A
    snd : B fst
-}
FlexVec = Σ ℕ (Vec Bool)

w : FlexVec
w = (0 , [])

-- jovo ora 2 perccel rovidebb
