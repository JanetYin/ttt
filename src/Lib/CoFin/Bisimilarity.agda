{-# OPTIONS --safe --guardedness #-}

module Lib.CoFin.Bisimilarity where

open import Lib.Conat.Type
open import Lib.Conat.Base
open import Lib.Maybe.Type
open import Lib.CoFin.Type
open import Lib.Unit.Type
open import Lib.Empty.Type

infix 4 _≈CoFin_ _≈CoFin'_
record _≈CoFin_ {n : ℕ∞} (k l : CoFin n) : Set

_≈CoFin'_ : {n : ℕ∞} → .⦃ e : IsNotZero∞ n ⦄ → Maybe (CoFin (predℕ∞ n)) → Maybe (CoFin (predℕ∞ n)) → Set
nothing ≈CoFin' nothing = ⊤
nothing ≈CoFin' just x = ⊥
just x ≈CoFin' nothing = ⊥
just x ≈CoFin' just y = x ≈CoFin y

record _≈CoFin_ {n} k l where
  coinductive
  field
    prove : _≈CoFin'_ {n} ⦃ inz k ⦄ (fpred∞ k) (fpred∞ l)

open _≈CoFin_ public
