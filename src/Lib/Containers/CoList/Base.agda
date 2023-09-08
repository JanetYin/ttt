{-# OPTIONS --safe --guardedness #-}

module Lib.Containers.CoList.Base where

open import Lib.Containers.CoList.Type
open import Lib.Containers.List.Type using (List)
import Lib.Containers.List.Type as L
open import Lib.Sum
open import Lib.Sigma
open import Lib.Unit
open import Lib.Nat
open import Lib.Conat
open import Lib.Level

[] : ∀{a}{A : Set a} → CoList A
headTail [] = []∞

infixr 5 _∷_
_∷_ : ∀{a}{A : Set a} → A → CoList A → CoList A
headTail (x ∷ xs) = x ∷∞ xs

replicate : ∀{i}{A : Set i} → ℕ → A → CoList A
replicate zero a = []
replicate (suc n) a = a ∷ replicate n a

coreplicate : ∀{i}{A : Set i} → ℕ∞ → A → CoList A
headTail (coreplicate n a) with pred∞ n
headTail (coreplicate n a) | zero∞ = []∞
headTail (coreplicate n a) | suc∞ n' = a ∷∞ coreplicate n' a

repeat : ∀{i}{A : Set i} → A → CoList A
repeat = coreplicate ∞

take : ∀{i}{A : Set i} → ℕ → CoList A → List A
take zero xs = L.[]
take (suc n) xs with headTail xs
take (suc n) xs | []∞ = L.[]
take (suc n) xs | y ∷∞ ys = y L.∷ take n ys

cotake : ∀{i}{A : Set i} → ℕ∞ → CoList A → CoList A
headTail (cotake n xs) with pred∞ n
headTail (cotake n xs) | zero∞   = []∞
headTail (cotake n xs) | suc∞ n' with headTail xs
headTail (cotake n xs) | suc∞ n' | []∞     = []∞
headTail (cotake n xs) | suc∞ n' | y ∷∞ ys = y ∷∞ cotake n' ys

length : ∀{i}{A : Set i} → CoList A → ℕ∞
pred∞ (length xs) with headTail xs
... | []∞ = zero∞
... | _ ∷∞ ys = suc∞ (length ys)

Unwrap-head-tail : ∀{a}{A : Set a} → CoList′ A → Set a
Unwrap-head-tail {a} {A} (inl _) = Lift a ⊤
Unwrap-head-tail {A = A} (inr _) = A × CoList A

unwrap-head-tail : ∀{a}{A : Set a} → (l : CoList′ A) → Unwrap-head-tail l
unwrap-head-tail (inl _) = _
unwrap-head-tail (inr x) = x