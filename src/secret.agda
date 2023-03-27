module secret where

open import lib

infixr 5 _∷_

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : A → {n : ℕ} → Vec A n → Vec A (suc n)

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just : A → Maybe A
