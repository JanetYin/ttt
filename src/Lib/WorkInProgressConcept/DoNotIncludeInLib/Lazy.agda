{-# OPTIONS --safe --guardedness #-}

module Lib.WorkInProgressConcept.DoNotIncludeInLib.Lazy where

open import Lib
open import Lib.Containers.List

data Lazy {i}(A : Set i) : Set i
record ∞Lazy {i}(A : Set i) : Set i

data Lazy A where
  now   : A → Lazy A
  later : ∞Lazy A → Lazy A

record ∞Lazy A where
  coinductive
  constructor delay
  field
    force : Lazy A

open ∞Lazy public

iteDelay : ∀{i j}{A : Set i}{B : Set j} → (A → B) → (∞Lazy A → B) → Lazy A → B
iteDelay f g (now x) = f x
iteDelay f g (later x) = g x

extract : ∀{i}{A : Set i}(n : ℕ)(da : Lazy A) → Maybe A
extract n       (now a)     = just a
extract zero    (later ∞da) = nothing
extract (suc n) (later ∞da) = extract n (force ∞da)

fmapLazy : ∀{i j}{A : Set i}{B : Set j} → (A → B) → Lazy A → Lazy B
fmap∞Lazy : ∀{i j}{A : Set i}{B : Set j} → (A → B) → ∞Lazy A → ∞Lazy B
fmapLazy f (now x) = now (f x)
fmapLazy f (later x) = later (fmap∞Lazy f x)
force (fmap∞Lazy f a) = fmapLazy f (later a)

data CoList {i}(A : Set i) : Set i where
  [] : CoList A
  _∷_ : A → Lazy (CoList A) → CoList A

repeat : ∀{i}{A : Set i} → A → Lazy (CoList A)
∞repeat : ∀{i}{A : Set i} → A → ∞Lazy (CoList A)

repeat a = now (a ∷ later (∞repeat a))
force (∞repeat a) = repeat a

replicate' : ∀{i}{A : Set i}(n : ℕ) → A → CoList A
replicate' zero a = []
replicate' (suc n) a = a ∷ now (replicate' n a)

takeLazy : ∀{i}{A : Set i} → ℕ → Lazy (CoList A) → Lazy (List A)
take∞Lazy : ∀{i}{A : Set i} → ℕ → ∞Lazy (CoList A) → ∞Lazy (List A)
takeLazy zero xs = now []
takeLazy (suc n) (now []) = now []
takeLazy (suc n) (now (x ∷ xs)) = let rec = takeLazy n xs in fmapLazy (x ∷_) rec
takeLazy (suc n) (later x) = later (take∞Lazy (suc n) x)
force (take∞Lazy n xs) = takeLazy n (force xs)

take' : ∀{i}{A : Set i} → ℕ → Lazy (CoList A) → List A
take' zero _ = []
take' (suc n) (now []) = []
take' (suc n) (now (x ∷ xs)) = x ∷ take' n xs
take' (suc n) (later x) with extract (suc n) (force x)
... | just [] = []
... | just (y ∷ ys) = y ∷ take' n ys
... | nothing = []

{-
_++_ : ∀{i}{A : Set i} → CoList A → CoList A → CoList A
[] ++ ys = ys
(x ∷ now xs) ++ ys = x ∷ now (xs ++ ys)
(x ∷ later xs) ++ ys = ?
-}
