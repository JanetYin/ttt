open import lib

-- parametrikus polimorfizmus, parametricity

-- f : {A B : Type} → A × B → A ⊎ B -- 2
-- f = λ w → (λ x → x) (inl (fst w))

-- fBool : Bool → Bool

-- f :: a -> a

-- f : {A : Type} → A → A        -- 1
-- f a = fst (a , tt)

-- f : (A : Type) → A            -- 0
-- f = {!!}

-- f : (A : Type) → A → (A → A)  -- 2
-- f = {!!}

-- f : (A : Type) → (A → A) → A -- 0
-- f = {!!}

-- f : (A : Type) → (A → A) → A → A  -- Nat Church-kodolasa
-- f = λ A s z → s (s (s z))

Nat' = (A : Type) → (A → A) → A → A

zero' : Nat'
zero' = λ A s z → z

suc' : Nat' → Nat'
suc' n = λ A s z → s (n A s z)

iteNat' : (B : Type) → (B → B) → B → Nat' → B
iteNat' = {!HF!}

-- 198? John Reynolds. Types, abstraction and parametric polymoprhism

infixr 4 _∷_

data Vec (A : Type) : ℕ → Type where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

data Fin : ℕ → Type where  -- Fin n = n-elemu halmaz
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

record Σ (A : Type)(B : A → Type) : Type where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

{-
   Π   Σ
   /\  /\
  /  \/  \
 →   ×    ⊎
-}

-- A, B : Type
-- A → B = (_ : A) → B

_² : Type → Type
A ² = Bool → A

_×'_ _×''_ : Type → Type → Type

A ×' B = (x : Bool) → if x then A else B

-- if_then_else_ Bool tipus iteratora
-- Bool tipus induction principle-je, indukcio muvelete, fuggo eliminator:
indBool : ∀{i}(A : Bool → Set i) → A true → A false → (t : Bool) → A t
indBool A u v true  = u
indBool A u v false = v

-- fst', snd', _,'_
fst' : {A B : Type} → A ×' B → A
fst' w = w true
snd' : {A B : Type} → A ×' B → B
snd' w = w false
_,'_ : {A B : Type} → A → B → A ×' B
(_,'_ {A}{B} a b) = indBool (λ x → if x then A else B) a b

-- Σ' : (A : Type) → (A → Typ) → Type
-- Σ' A B = (f : (x : Bool) → if x then A else B (f true))

A ×'' B = Σ A (λ _ → B)

_⊎'_ : Type → Type → Type
A ⊎' B = Σ Bool λ x → if x then A else B

-- inl', inr', case'

-- Bool ≅ Fin 2, isomorphism

-- Fin m ⊎ Fin n ≅ Fin (m + n) isomorphism

-- Σ (Fin n) λ i → Fin (a i) ≅ Fin (Σℕ n a)    Σℕ n a = a 0 + a 1 + ... + a (n - 1)
-- (i : Fin n) → Fin (a i) ≅ Fin (Πℕ n a)      Πℕ n a = a 0 * a 1 * ... * a (n - 1)
