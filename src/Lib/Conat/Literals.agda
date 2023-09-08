{-# OPTIONS --safe --guardedness #-}

module Lib.Conat.Literals where

open import Lib.Conat.Type
open import Lib.Conat.Base
open import Lib.Unit.Type public
open import Agda.Builtin.FromNat public

instance
  Numℕ∞ : Number ℕ∞
  Number.Constraint Numℕ∞ _ = ⊤
  Number.fromNat Numℕ∞ n = embed n