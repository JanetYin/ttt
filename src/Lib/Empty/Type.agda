{-# OPTIONS --safe #-}

module Lib.Empty.Type where

open import Lib.Irrelevant

private
  data Empty : Set where

⊥ : Set
⊥ = Irrelevant Empty

{-# DISPLAY Irrelevant Empty = ⊥ #-}