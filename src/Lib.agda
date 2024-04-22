{-# OPTIONS --safe --guardedness #-}

module Lib where

-- There are only container's types imported.
-- They have to be opened manually,
-- because there are a lot of functions that have the same name.

open import Lib.Class public
open import Lib.Level public
open import Lib.Function public
open import Lib.Reflection public
  renaming (irrelevant to irrelevant-in-reflection)
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
  renaming (_+_ to _+∞_ ; _+'_ to _+∞'_ ; _*_ to _*∞_ ; idr+ to idr+∞; _^_ to _^∞_)
open import Lib.Sum public
  renaming (map to map⊎)
open import Lib.Fin public
open import Lib.CoFin public
open import Lib.Equality public
open import Lib.Dec public
open import Lib.Maybe public
open import Lib.Ordering public
  renaming (_≟_ to _≟Ordering_)
open import Lib.UnitOrEmpty public

------------------------------------------------------------
-- Change when needed
-- open import Lib.Product public
  -- renaming (map to map×)
open import Lib.Sigma public
  renaming (map to mapΣ)

------------------------------------------------------------
-- Containers

open import Lib.Containers.List.Type hiding (module List) public
module List where
  open import Lib.Containers.List hiding (module List) public

open import Lib.Containers.Stream.Type hiding (module Stream) public
module Stream where
  open import Lib.Containers.Stream hiding (module Stream) public

open import Lib.Containers.CoList.Type hiding (module CoList; _∷_; []; head; tail) public
module CoList where
  open import Lib.Containers.CoList hiding (module CoList) public

open import Lib.Containers.Vector.Type hiding (module Vec) public
module Vec where
  open import Lib.Containers.Vector hiding (module Vec) public

open import Lib.Containers.CoVector.Type hiding (module CoVec; []) public
module CoVec where
  open import Lib.Containers.CoVector hiding (module CoVec) public

open import Lib.Containers.HList.Type hiding (module HList) public
module HList where
  open import Lib.Containers.HList hiding (module HList) public
