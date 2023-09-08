module ea06 where

open import lib hiding (Σ)
open import ea05

-- Vec, Fin

-- Π types, szabalyok, special case simply typed
{-
Π fuggo fuggveny

A : Set   B : A → Set
---------------------
 (x : A) → B x : Set             masik jeloles: Π A B

ℕ : Set     Vec Bool : ℕ → Set
------------------------------
(n : ℕ) → Vec Bool n

Γ ⊢ t : (x : A) → B x    Γ ⊢ t' : A         Γ,x:A ⊢ t : B x
------------------------------------    -------------------------
        Γ ⊢ t t' : B t'                 Γ ⊢ (λ x → t) : (x:A)→B x

t : (n : ℕ) → Vec Bool n     3 : ℕ             n:ℕ⊢t : Vec Bool n
----------------------------------      -------------------------------
         t 3 : Vec Bool 3                (λ n → t) : (n:ℕ) → Vec Bool n

                                           t : (x:A)→B x
--------------------                      ---------------η (egyediseg)
(λ x → t) u = t[x↦u]   (β, szamitasi)      t = λ x → t x

-}

-- if_then_else_ = fold Bool-ra / Bool iteratora / Bool rekurzora / nemdependens eliminator
-- fuggo if-then-else = eliminator / dependens eliminator
elimBool : (A : Bool → Set) → A true → A false → (b : Bool) → A b
elimBool A t f true  = t
elimBool A t f false = f

if_then_else'_ : {A : Set} → Bool → A → A → A
if_then_else'_ {A} b t f = elimBool (λ _ → A) t f b

-- magassagEsNem : ℕ × Bool
Magassag = ℕ
Nem      = Bool
magassagEsNem : (b : Bool) → if b then Magassag else Nem
magassagEsNem false = true
magassagEsNem true = 176


-- Σ types, szabalyok, FlexVec

record Σ (A : Set)(B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ

Date = ℕ
Return = Bool

dateOfTravel : Σ Return (λ b → if b then Date × Date else Date)
fst dateOfTravel = true
snd dateOfTravel = 20230410 , 20230412

FlexVec : Set → Set
FlexVec A = Σ ℕ (Vec A)
w : Σ ℕ (Vec Bool) -- ≅ List Bool
w = 5 , (true ∷ false ∷ true ∷ false ∷ false ∷ [])

-- ((_ : A) → B) = (A → B)

_×'_ : Set → Set → Set
A ×' B = Σ A (λ _ → B)

fst' : {A B : Set} → A ×' B → A
fst' = fst
{-
             ∞
             Σ (i*2) = 0 * 2 + 1*2 + 2*2 + 3*2 + ...
            i=0       

    Σ B      Σ (λ n → Fin n × Bool) = Fin 0 × Bool ⊎ Fin 1 × Bool ⊎ Fin 2 × Bool ⊎ .... 
    A        ℕ

     A = {a1,a2,a3,a4}
     Σ A B ≅ B a1 ⊎ B a2 ⊎ B a3 ⊎ B a4
     Σ Bool B ≅ B true ⊎ B false
     Σ Return (λ b → if b then Date × Date else Date) ≅ (Date × Date) ⊎ Date

Σ \GS
∑ \sum
-}

-- egyszeru tipusok: ×, ⊎, →
-- fuggo tipusok:    Σ, ?  Π

_⊎'_ : Set → Set → Set  -- A ⊎' B ≅ A ⊎ B
A ⊎' B = Σ Bool λ b → if b then A else B

inl' : {A B : Set} → A → A ⊎' B
inl' a = true , a

inr' : {A B : Set} → B → A ⊎' B
inr' b = false , b

case' : {A B C : Set} → A ⊎' B → (A → C) → (B → C) → C
case' (false , x) f g = g x
case' (true  , x) f g = f x

{-
    Π     Σ
   / \   / \
  /   \ /   \
 →     ×     ⊎
-}

_×''_ : Set → Set → Set
A ×'' B = (b : Bool) → if b then A else B

fst'' : {A B : Set} → A ×'' B → A
fst'' w = w true

snd'' : {A B : Set} → A ×'' B → B
snd'' w = w false

_,''_ : {A B : Set} → A → B → A ×'' B
(a ,'' b) false = b
(a ,'' b) true = a

-- simple arithmetic: (Fin m ⊎ Fin n) ↔ Fin (m + n)
--                    (Fin m × Fin n) ↔ Fin (m * n)
--                    (Fin m → Fin n) ↔ Fin (n ^ m)

bool-eq : {m n : ℕ} → Bool ↔ Fin 2
fst bool-eq false = zero
fst bool-eq true = suc zero
snd bool-eq zero = false
snd bool-eq (suc zero) = true

five-eq : Fin 2 ⊎ Fin 3 ↔ Fin (2 + 3)
fst five-eq (inl zero)                   = zero
fst five-eq (inl (suc zero))             = suc zero
fst five-eq (inr zero)                   = suc (suc zero)
fst five-eq (inr (suc zero))             = suc (suc (suc zero))
fst five-eq (inr (suc (suc zero)))       = suc (suc (suc (suc zero)))
snd five-eq zero                         = (inl zero)            
snd five-eq (suc zero)                   = (inl (suc zero))      
snd five-eq (suc (suc zero))             = (inr zero)            
snd five-eq (suc (suc (suc zero)))       = (inr (suc zero))      
snd five-eq (suc (suc (suc (suc zero)))) = (inr (suc (suc zero)))

inlf : {m n : ℕ} → Fin m → Fin (m + n) -- induction on i
inlf zero = zero
inlf (suc i) = suc (inlf i)

inrf : {m n : ℕ} → Fin n → Fin (m + n) -- induction on m
inrf {zero} i = i
inrf {suc m} i = suc (inrf {m} i)

casef : {m n : ℕ}{C : Set} → Fin (m + n) → (Fin m → C) → (Fin n → C) → C
casef {zero} x f g = g x
casef {suc m} zero f g = f zero
casef {suc m} (suc i) f g = casef {m} i (λ j → f (suc j)) g

sum-eq : {m n : ℕ} → (Fin m ⊎ Fin n) ↔ Fin (m + n)
fst sum-eq (inl x) = inlf x
fst sum-eq (inr x) = inrf x
snd (sum-eq {m}{n}) w = casef {m}{n} w inl inr

-- HF, kicsit nehez
prod-eq : {m n : ℕ} → (Fin m × Fin n) ↔ Fin (m * n)
prod-eq = {!!}

_^_ : ℕ → ℕ → ℕ
a ^ zero    = 1
a ^ (suc n) = a * a ^ n

-- HF, kicsit nehez
exp-eq : {m n : ℕ} → (Fin m → Fin n) ↔ Fin (n ^ m)
exp-eq = {!!}

--                                           i<n
-- Σℕ n a = a 0 + a 1 + a 2 + ... + a (n-1) = Σ a(i)
--                                           i=0
Σℕ : (n : ℕ) → (Fin n → ℕ) → ℕ
Σℕ zero    a = 0
Σℕ (suc n) a = a zero + Σℕ n (λ i → a (suc i))

--                                           i<n
-- Πℕ n a = a 0 * a 1 * a 2 * ... * a (n-1) = Π a(i)
--                                           i=0
Πℕ : (n : ℕ) → (Fin n → ℕ) → ℕ
Πℕ zero    a = 1
Πℕ (suc n) a = a zero * Σℕ n (λ i → a (suc i))

-- pelda: n = 3, a 0 = 3, a 1 = 2, a 2 = 2, describe the elements
-- pi-eq : ((i : Fin 3) → a i) ≅ 3 * 2 * 2

pi-eq : (n : ℕ)(a : Fin n → ℕ) →  ((i : Fin n)   → Fin (a i)) ↔ Fin (Πℕ n a)
pi-eq = {!!}

-- sigma-eq : Σ (Fin 3) (Fin (a i)) = 3 + 2 + 2

sigma-eq : (n : ℕ)(a : Fin n → ℕ) → (Σ (Fin n) λ i → Fin (a i)) ↔ Fin (Σℕ n a)
sigma-eq = {!!}

-- kovetkezo ora 11 perccel rovidebb
