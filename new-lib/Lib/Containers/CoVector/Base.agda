{-# OPTIONS --safe --guardedness #-}

module Lib.Containers.CoVector.Base where

open import Lib.Containers.CoVector.Type
open import Lib.Conat renaming (_+_ to _+∞_)
open import Lib.Nat

open import Lib.Unit
open import Lib.Empty
open import Lib.Sigma hiding (map)
open import Lib.Sum hiding (map)
open import Lib.Equality

[] : ∀{i}{A : Set i} → CoVec A 0
head [] ⦃ () ⦄
tail [] ⦃ () ⦄

replicate : ∀{i}{A : Set i} → (n : ℕ∞) → A → CoVec A n
head (replicate n a) with pred∞ n
... | suc∞ b = a
tail (replicate n a) with pred∞ n
... | suc∞ b = replicate b a

repeat : ∀{i}{A : Set i} → A → CoVec A ∞
repeat = replicate ∞

map : ∀{i j}{A : Set i}{B : Set j}{n : ℕ∞} → 
            (A → B) → CoVec A n → CoVec B n
head (map f xs) = f (head xs)
tail (map f xs) = map f (tail xs)

infixr 5 _++_
_++_ : ∀{i}{A : Set i}{n m : ℕ∞} → CoVec A n → CoVec A m → CoVec A (n +∞ m)
head (_++_ {n = n} {m} xs ys) with pred∞ n | head xs
head (_++_ {n = n} {m} xs ys) | zero∞ | _ with pred∞ m | head ys
head (_++_ {n = n} {m} xs ys) | zero∞ | _ | suc∞ b | hy = hy
head (_++_ {n = n} {m} xs ys) | suc∞ b | h = h
tail (_++_ {n = n} {m} xs ys) with pred∞ n | (λ x → tail xs ⦃ x ⦄)
tail (_++_ {n = n} {m} xs ys) | zero∞ | _ with pred∞ m | (λ x → tail ys ⦃ x ⦄)
tail (_++_ {n = n} {m} xs ys) | zero∞ | _ | suc∞ b | ty = ty tt
tail (_++_ {n = n} {m} xs ys) | suc∞ b | tx = tx tt ++ ys

substCoVec : ∀{i}{A : Set i}{n m : ℕ∞} → n ≈ℕ∞ m → CoVec A n → CoVec A m
substCoVec' : ∀{i}{A : Set i}{n m : ℕ∞'} → n ≈ℕ∞′′ m → CoVec A (pred∞'' n) → CoVec A (pred∞'' m)
substCoVec' {n = zero∞} {zero∞} e xs = xs
substCoVec' {n = suc∞ a} {suc∞ b} e xs = substCoVec {n = a} {pred∞'' (suc∞ b)} e xs
head (substCoVec {n = n} {m} e xs) ⦃ eq ⦄ with pred∞ n in eq1 | pred∞ m in eq2 | head xs
head (substCoVec {n = n} {m} e xs) ⦃ eq ⦄ | zero∞ | zero∞ | h = h ⦃ eq ⦄
head (substCoVec {n = n} {m} e xs) | suc∞ b | zero∞ | h = h
head (substCoVec {n = n} {m} e xs) | zero∞ | suc∞ b | h with transℕ∞' (transℕ∞' (≡→≈ℕ∞′′ (sym eq1)) (prove e)) (≡→≈ℕ∞′′ eq2)
head (substCoVec {n = n} {m} e xs) | zero∞ | suc∞ b | h | ()
head (substCoVec {n = n} {m} e xs) | suc∞ b₁ | suc∞ b | h = h
tail (substCoVec {n = n} {m} e xs) with pred∞ n in eq1 | pred∞ m in eq2 | (λ x → tail xs ⦃ x ⦄)
tail (substCoVec {n = n} {m} e xs) | zero∞ | suc∞ b | t with transℕ∞' (transℕ∞' (≡→≈ℕ∞′′ (sym eq1)) (prove e)) (≡→≈ℕ∞′′ eq2)
tail (substCoVec {n = n} {m} e xs) | zero∞ | suc∞ b | t | ()
tail (substCoVec {n = n} {m} e xs) | suc∞ n' | suc∞ m' | t = substCoVec {n = n'} {m'} (transℕ∞' (transℕ∞' (≡→≈ℕ∞′′ (sym eq1)) (prove e)) (≡→≈ℕ∞′′ eq2)) (t tt)

take : ∀{i}{A : Set i}(n : ℕ∞){m : ℕ∞} → CoVec A (n +∞ m) → CoVec A n
head (take n {m} xs) ⦃ e ⦄ with pred∞ n | weakenℕ∞ n m e | head xs
... | zero∞  | p | x = x ⦃ p ⦄
... | suc∞ _ | _ | x = x
tail (take n {m} xs) with pred∞ n | (λ x → tail xs ⦃ x ⦄)
tail (take n {m} xs) | zero∞ | _ = substCoVec 0=0 []
tail (take n {m} xs) | suc∞ n' | t = take n' {m} (t tt)