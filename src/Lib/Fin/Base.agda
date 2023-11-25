{-# OPTIONS --safe #-}

module Lib.Fin.Base where

open import Lib.Equality
open import Lib.Nat
open import Lib.Fin.Type

toℕ : {n : ℕ} → Fin n → ℕ
toℕ fzero    = 0
toℕ (fsuc i) = suc (toℕ i)

Fin' : {n : ℕ} → Fin n → Set
Fin' i = Fin (toℕ i)

cast-Fin : ∀{m n} → .(m ≡ n) → Fin m → Fin n
cast-Fin {zero}  {zero}  eq k        = k
cast-Fin {suc m} {suc n} eq fzero    = fzero
cast-Fin {suc m} {suc n} eq (fsuc k) = fsuc (cast-Fin (cong pred' eq) k)

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero    = fzero
fromℕ (suc n) = fsuc (fromℕ n)