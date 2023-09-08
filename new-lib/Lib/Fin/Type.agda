{-# OPTIONS --safe #-}

module Lib.Fin.Type where

open import Lib.Nat.Type

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ}(i : Fin n) → Fin (suc n)