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

raiseᵣ : {m : ℕ}(n : ℕ) → Fin m → Fin (n + m)
raiseᵣ zero m' = m'
raiseᵣ (suc n) m' = fsuc (raiseᵣ n m')

raiseₗ : {m : ℕ} → Fin m → (n : ℕ) → Fin (m + n)
raiseₗ {suc m} fzero n = fzero
raiseₗ {suc m} (fsuc m') n = fsuc (raiseₗ {m} m' n)

elim-Fin : ∀{ℓ}{k : ℕ}(P : {n : ℕ} → Fin n → Set ℓ) →
  (pzero : {n : ℕ} → P (fzero {n})) →
  (psuc : {n : ℕ}{f : Fin n} → P f → P (fsuc f)) →
  (f : Fin k) →
  P f
elim-Fin P pzero psuc fzero = pzero
elim-Fin P pzero psuc (fsuc f) = psuc (elim-Fin P pzero psuc f)
