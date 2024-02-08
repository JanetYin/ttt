{-# OPTIONS --safe #-}

module Lib.Maybe.Type where

data Maybe {a} (A : Set a) : Set a where
  just : A → Maybe A
  nothing : Maybe A
