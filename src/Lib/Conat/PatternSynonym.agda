{-# OPTIONS --safe #-}

module Lib.Conat.PatternSynonym where

open import Lib.Maybe.Type

pattern zero∞ = nothing
pattern suc∞ n = just n