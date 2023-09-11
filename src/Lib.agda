{-# OPTIONS --safe --guardedness #-}

module Lib where

-- There are no lists, vectors, streams imported by default.
-- They have to be imported manually,
-- because there are a lot of functions that have the same name.

open import Lib.Level public
open import Lib.Unit public
  renaming (_≟_ to _≟⊤_)
open import Lib.Empty public
  renaming (_≟_ to _≟⊥_)
open import Lib.Nat public
  renaming (_≟_ to _≟ℕ_)
open import Lib.Bool public
  renaming ( contradiction to contradictionᵇ
           ; contraposition to contrapositionᵇ
           ; _≟_ to _≟ᵇ_)
open import Lib.Conat public
  renaming (_+_ to _+∞_ ; idr+ to idr+∞)
open import Lib.Sum public
  renaming (map to map⊎)
open import Lib.Fin public
open import Lib.Equality public
open import Lib.Dec public
open import Lib.Maybe public

------------------------------------------------------------
-- Change when needed
open import Lib.Product public
  renaming (map to map×)
-- open import Lib.Sigma public
  -- renaming (map to mapΣ)