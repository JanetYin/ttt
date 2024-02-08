{-# OPTIONS --safe #-}

module Lib.Ordering.Type where

data Ordering : Set where
  LT EQ GT : Ordering
