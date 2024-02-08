{-# OPTIONS --safe --guardedness #-}

module LibTypes where

-- There are no lists, vectors, streams imported by default.
-- They have to be imported manually,
-- because there are a lot of functions that have the same name.

open import Lib.Level public
open import Lib.Unit.Type public
open import Lib.Empty.Type public
open import Lib.Nat.Type public
open import Lib.Nat.Literals public
open import Lib.Bool.Type public
open import Lib.Conat.Type public
open import Lib.Conat.Literals public
open import Lib.Sum.Type public
open import Lib.Fin.Type public
open import Lib.Fin.Literals public
open import Lib.Equality.Type public
open import Lib.Dec public
open import Lib.Maybe.Type public

------------------------------------------------------------
-- Change when needed
open import Lib.Product.Type public
-- open import Lib.Sigma.Type public