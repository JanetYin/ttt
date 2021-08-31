module x where

data Bool : Set where
  true false : Bool

if_then_else_ : ∀{i}{A : Set i}(t : Bool)(u v : A) → A
if true then u else v = u
if false then u else v = v

not : Bool → Bool
not = λ x → if x then false else true

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

rec : ∀{i}{A : Set i}(u : A)(v : A → A)(t : ℕ) → A
rec u v zero = u
rec u v (suc t) = v (rec u v t)

data Eq {i}(A : Set i)(a : A) : A → Set where
  refl : Eq A a a

1+_+3*_ : ℕ → (ℕ → ℕ)
{- END FIX -}
1+_+3*_ = λ x y → rec (suc x) (λ w → suc (suc (suc w))) y 

{- BEGIN FIX -}
isodd : ℕ → Bool
{- END FIX -}
isodd = {!!}

-- tests

{- BEGIN FIX -}
test1 : Eq ℕ (1+ 3 +3* 5) 19
test1 = refl

test2 : Eq ℕ (1+ 4 +3* 2) 11
test2 = refl

test3 : Eq Bool (isodd 2) false
test3 = refl

test4 : Eq Bool (isodd 3) true
test4 = refl
{- END FIX -}
