open import lib hiding (_⊎_; inl; inr; case)

infixr 4 _∷_

-- fuggo tipus: A : B → Type

data List (A : Type) : Type where
  []  : List A
  _∷_ : A → List A → List A

data Vec (A : Type) : ℕ → Type where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)


-- Vec ℕ : ℕ → Type
-- Vec ℕ 0 : Type  <- 0-hosszu vektorok tipusa
0hosszuvektor : Vec ℕ 0
0hosszuvektor = []
-- Vec ℕ 2 : Type <- 2-hosszu vektorok tipusa
2hosszuvektor : Vec ℕ (1 + 1)
2hosszuvektor = _∷_ {ℕ}{1} 3 (_∷_ {ℕ}{0} 2 []) -- 3 ∷ 2 ∷ []
-- [] : Vec A 0
-- _∷_ : A → Vec A n → Vec A (1 + n)
3hosszuvektor : Vec ℕ 3
3hosszuvektor = 19 ∷ 2hosszuvektor
-- Vec A : ℕ → Type
-- Vec : Type → ℕ → Type

-- Fin : ℕ → Type -- Fin n az az n-elemu tipus, Fin 0 = ures tipus, Fin 1 = egyelemu tipus, Fin 2 = ketelemu tipus
-- Fin x
-- polimorf tipusok: (A B : Type) → A × B ↔ B × A

-- Vec, Fin, polymorphic types

-- zeroes-l, zeroes-v

zeroes-l : ℕ → List ℕ
zeroes-l zero    = []
zeroes-l (suc n) = zeroes-l n

zeroes-v : (n : ℕ) → Vec ℕ n    -- fuggo fuggveny
zeroes-v zero    = []
zeroes-v (suc n) = 0 ∷ zeroes-v n

append-l : (A : Type) → List A → List A → List A
append-l A [] ys = ys
append-l A (x ∷ xs) ys = x ∷ append-l A xs ys

append-v : (A : Type)(m n : ℕ) → Vec A m → Vec A n → Vec A (m + n)
append-v A 0       n []       ys = ys
append-v A (suc m) n (x ∷ xs) ys = {!!}

t : Vec ⊥ 10 → Vec ⊥ 10 → Vec ⊥ 20
t = append-v ⊥ 10 10

-- t' : (xs : Vec ⊥ 10) → t xs xs ≡ append-v ⊥ 0 20 [] ...

-- append-l, append-v, test, explicit length, implicit, check type of _∷_

data Maybe (A : Type) : Type where
  Just : A → Maybe A
  Nothing : Maybe A

_!!l_ : {A : Type} → List A → ℕ → Maybe A
[] !!l zero = Nothing
[] !!l suc n = Nothing
(x ∷ xs) !!l zero = Just x
(x ∷ xs) !!l suc n = xs !!l n

-- data ℕ : Type where
--   zero : ℕ
--   suc  : ℕ → ℕ

data Fin : ℕ → Type where  -- Fin n = n-elemu halmaz
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

-- Fin 0 = {}
-- Fin 1 = Fin (suc 0) = { zero 0 }
--                         ^ : Fin (suc 0)
-- Fin 2 = { zero 1 , suc 1 (zero 0) }
-- Fin 3 = { zero 2 , suc 2 (zero 1) , suc 2 (suc 1 (zero 0))}
-- Fin 4 = { zero 3 , suc 3 (zero 2) , suc 3 (suc 2 (zero 1)) , suc 3 (suc 2 (suc 1 (zero 0))) }
-- ...
-- Fin0, Fin1, Fin2, Fin3,

-- Fin 0 = {}
-- Fin 1 = { zero }
-- Fin 2 = { zero , suc zero }
-- Fin 3 = { zero , suc zero , suc (suc zero)}
-- Fin 4 = { zero , suc zero , suc (suc zero) , suc (suc (suc zero)) }
-- ...
-- Fin0, Fin1, Fin2, Fin3,

fin3 : Fin 3
fin3 = suc (suc zero)

fin4 : Fin 4
fin4 = suc (suc zero)

-- _!!_ : List A → ℕ → A, Maybe, vector version with Fin

_!!_ : {A : Type}{n : ℕ} → Vec A n → Fin n → A
(x ∷ xs) !! zero = x
(x ∷ xs) !! suc i = xs !! i  -- (+) 2    (+2)  (_+ 2) (λ x → x + 2)
-- (A → B) = (x : A) → B    Π tipus
-- (x : A) → B x
-- (n : ℕ) → Vec A n
-- A = ℕ
-- B : ℕ → Type
-- B = Vec A

-- Π → 
-- Σ ×
--   ⊎
-- ℕ × List Bool = { (1 , true ∷ []) , (1 , []) , (3 , false ∷ true ∷ []) }
-- Σ ℕ (Vec Bool) = { (1 , true ∷ []) , (1 , false ∷ []) , (3 , false ∷ true ∷ false ∷ []) , ... }

record Σ (A : Type)(B : A → Type) : Type where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

pl1 pl2 : Σ ℕ (Vec Bool)
pl1 = (1 , true ∷ [])
pl2 = (0 , [])

FlexVec : Type → Type
FlexVec A = Σ ℕ (Vec A) -- ≅ List A

{-
   Π   Σ
   /\  /\
  /  \/  \
 →   ×    ⊎
-}

_⊎_ : Type → Type → Type
A ⊎ B = Σ Bool (if_then A else B) -- A ⊎ B = { (0,a) | a ∈ A} ∪ { (1,b) | b ∈ B}

inl : ∀{A B} → A → A ⊎ B
inl a = true , a

inr : ∀{A B} → B → A ⊎ B
inr b = false , b

case : ∀{A B}(C : A ⊎ B → Type)
  (w : A ⊎ B) →
  ((a : A) → C (inl a)) →
  ((b : B) → C (inr b)) →
  C w
case C (true  , a) f g = f a
case C (false , b) f g = g b


-- Σ, special case, FlexVec, _⊎_ defined using Σ,inj₁,inj₂,case, × using Π

-- Bool ≅ Fin 2, isomorphism
-- Fin m ⊎ Fin n ≅ Fin (m + n) etc, isomorphism
-- Σ (Fin n) λ i → Fin (a i) ≅ Fin (Σℕ n a)    Σℕ n a = a 0 + a 1 + ... + a (n - 1)
-- (i : Fin n) → Fin (a i) ≅ Fin (Πℕ n a)      Πℕ n a = a 0 * a 1 * ... * a (n - 1)
