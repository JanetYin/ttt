{-# OPTIONS --safe #-}

module Lib.Fin.Properties where

open import Lib.Fin.Type
open import Lib.Empty
open import Lib.Equality
open import Lib.Nat

¬Fin0 : ¬ Fin 0
¬Fin0 ()

Fin1-η : (a b : Fin 1) → a ≡ b
Fin1-η fzero fzero = refl