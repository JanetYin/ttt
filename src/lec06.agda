{-
quiz: there are more elements in (ℕ → Bool) than ℕ. Cantor's diagonal argument.

there is no surjection from ℕ to (ℕ → Bool):

  
0  01010110100101010101001010...
1  00000000000000000000000000...
2  10000000000000100000000000...
3  11111111111111111111111110...
4  11101010100000000000000000...
5  00000000000111111111111111...
6  11111110000010101010010000...
...

there is a sequence which is not in the list:

   1110010....................  <- this is different from the n^th sequence in the n^th postition

-}

-- Π, Σ, special cases

-- Π    (n : ℕ) → Vec Bool n,   Π(n:ℕ).Vec Bool n,    (A:Set)→A→A,  (b:Bool) → if b then Picture else Book

-- built-in: Set, →, record, data

module lec06 where

module test where
  record Σ (A : Set)(B : A → Set) : Set where
    field
      fst : A
      snd : B fst
  open Σ

  _,_ : {A : Set}{B : A → Set}(a : A) → B a → Σ A B
  fst (a , b) = a
  snd (a , b) = b

open import Lib
open import Lib.Containers.List
open import Lib.Containers.Vector

Bitmap : Set
Bitmap = Σ ℕ λ width → Σ ℕ λ height → Vec (Fin 8) (width * height)

img1 : Bitmap
img1 = (1 , (2 , fzero ∷ ((fsuc (fsuc fzero)) ∷ [])))

StupidBitmap : Set
StupidBitmap = ℕ × ℕ × List (Fin 8)
-- StupidBitmap = ℕ × ℕ × (ℕ → Fin 8)

img2 : StupidBitmap
img2 = (1 , (2 , []))

Date = ℕ
TrainBooking : Set
TrainBooking = Σ Bool λ return? → if return? then (Date × Date) else Date

travel : TrainBooking
travel = true , 4 , 7

FlexVec : Set → Set
-- FlexVec A = Σ ℕ (λ n → Vec A n)
FlexVec A = Σ ℕ (Vec A)

-- FlexVec A ≅ List A

-- Python programming
-- dynamic type: 

PythonProg : Set₁
PythonProg = Σ Set (λ A → A)

aPythonNumber : PythonProg
aPythonNumber = ℕ , 3

pythonAddition : PythonProg → PythonProg → PythonProg
pythonAddition (A , a) (B , b) = {!!}
-- in Java I can do a.instanceOf(ℕ) which is the same as matching on A whether it is ℕ...

-- "expression problem"

-- f : (A : Set) → A → A   <- parametricity, abstraction, parametric polymorphism

data PythonType : Set where
  bool : PythonType
  int  : PythonType
  _⇒_  : PythonType → PythonType → PythonType
  prod : PythonType → PythonType → PythonType
  runtimeError : PythonType

-- elements of the PythonType
El : PythonType → Set
El bool = Bool
El int = ℕ
El (a ⇒ b) = El a → El b
El (prod a b) = El a × El b
El runtimeError = ⊤

PythonPrg : Set
PythonPrg = Σ PythonType λ a → El a

pythonAdditionReal : PythonPrg → PythonPrg → PythonPrg
pythonAdditionReal (int , a) (int , b) = int , a + b
pythonAdditionReal (_   , a) (_   , b) = runtimeError , tt

-- →<-Π->×<-Σ->⊎

{-
product   sum
   Π     Σ
  / \   / \
 /   \ /   \
→     ×     ⊎
-}

-- (Bool → A)                        ≅ (A × A)
-- ((b : Bool) → if b then A else B) ≅ (A × B)

module ×fromΠ (A B : Set) where
  f : ((b : Bool) → if b then A else B) → (A × B)
  f α = (α true) , (α false)

  g : (A × B) → ((b : Bool) → if b then A else B)
  g ab false = snd ab
  g ab true = fst ab

-- Σ Bool λ x → if x then A else B  ≅  A ⊎ B
-- TrainBooking = Σ Bool λ return? → if return? then (Date × Date) else Date
-- (Date × Date) ⊎ Date

-- A ⊎ B ⊎ C ≅ Σ (Fin 3) "[A,B,C]"
-- A0 ⊎ A1 ⊎ ... ⊎ An ≅ Σ (Fin n) λ n → A n
-- A0 ⊎ A1 ⊎ ...      ≅ Σ ℕ λ n → A n                      A : ℕ → Set     THIS IS WHY WE LIKE Σ

-- A × B × C ≅ (i : Fin 3) → "[A,B,C]" i
-- A 0 × A 1 × A 2 × ....  ≅  (n : ℕ) → A n                A : ℕ → Set

module Fin+ where -- Fin m ⊎ Fin n ≅ Fin (m + n)
  fl : {m n : ℕ} → Fin m  → Fin (m + n)
  -- fl {suc m}{n}(fzero {m}) = fzero {m + n}
  fl fzero = fzero
  fl (fsuc i) = fsuc (fl i)

  fr : {m n : ℕ} → Fin n  → Fin (m + n)
  fr {zero}  i = i
  fr {suc m} i = fsuc (fr {m} i)

  f : {m n : ℕ} → Fin m ⊎ Fin n → Fin (m + n)
  f (inl a) = fl a
  f (inr b) = fr b

  -- Fin 3 ⊎ Fin 2 → Fin 5
  -- inl 0 ↦ 0        inl (fzero {2}) ↦ fzero {4}
  -- inl 1 ↦ 1
  -- inl 2 ↦ 2
  -- inr 0 ↦ 3
  -- inr 1 ↦ 4
  -- inr i ↦ fsuc (fsuc (fsuc i))

  casef : {m n : ℕ}{C : Set} → (Fin m → C) → (Fin n → C) → Fin (m + n) → C
  casef = {!!} -- exercise for home

  g : {m n : ℕ} → Fin (m + n) → Fin m ⊎ Fin n
  g i = casef inl inr i

-- Fin m ⊎ Fin n ≅ Fin (m + n)
-- Fin m × Fin n ≅ Fin (m * n)
-- Fin m → Fin n ≅ Fin (n ^ m)

Πℕ : (n : ℕ) → (Fin n → ℕ) → ℕ
Πℕ zero    f = 1
Πℕ (suc n) f = f fzero * Πℕ n λ i → f (fsuc i)

-- f : Fin n → ℕ
-- (i : Fin n) → Fin (f i)  ≅  Fin (Πℕ n f)

⌜_⌝ : {n : ℕ} → Fin n → ℕ
⌜ fzero ⌝ = zero
⌜ fsuc i ⌝ = suc ⌜ i ⌝

fac : ℕ → ℕ
fac n = Πℕ n (λ i → suc ⌜ i ⌝)

Σℕ : (n : ℕ) → (Fin n → ℕ) → ℕ
Σℕ zero    f = 1
Σℕ (suc n) f = f fzero + Σℕ n λ i → f (fsuc i)

-- f : Fin n → ℕ
-- Σ (Fin n) λ i → Fin (f i)  ≅  Fin (Σℕ n f)

-- next class is 4 minutes shorter

-- ...
-- alternative implementation of Vec?
