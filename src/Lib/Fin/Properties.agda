{-# OPTIONS --safe #-}

module Lib.Fin.Properties where

open import Lib.Fin.Type
open import Lib.Fin.Base
open import Lib.Empty
open import Lib.Equality
open import Lib.Nat

¬Fin0 : ¬ Fin 0
¬Fin0 ()

Fin1-η : (a b : Fin 1) → a ≡ b
Fin1-η fzero fzero = refl

finsuc-injective : {n : ℕ}{x y : Fin n} → fsuc x ≡ fsuc y → x ≡ y
finsuc-injective {x = x} e = cong (p x) e where
  p : {k : ℕ} → Fin k → Fin (suc k) → Fin k
  p k fzero = k
  p _ (fsuc x) = x