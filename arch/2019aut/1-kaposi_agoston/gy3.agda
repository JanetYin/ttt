module gy3 where

open import lib

-- HW
odd : ℕ → Bool
odd = {!!}

and : Bool → Bool → Bool
and = λ x y → if x then y else false

not : Bool → Bool
not = λ b → if b then false else true

pred : ℕ → ℕ
pred = λ n → primrec 0 (λ n' _ → n') n

_+_ : ℕ → ℕ → ℕ
_+_ = λ x y → primrec x (λ y' fy' → suc fy') y

-- HW
-- sum n is the sum of the natural numbers from 0 to n.
-- sum 0 = 0, sum 1 = 1, sum 2 = 3, sum 3 = 6, sum 4 = 10, ...
sum : ℕ → ℕ
sum = {!!}

-- HW
_*_ : ℕ → ℕ → ℕ
_*_ = {!!}

_^_ : ℕ → ℕ → ℕ
_^_ = {!!}

squaresum : ℕ → ℕ
squaresum = {!!}

-- arithmetic progression
-- a0
-- common difference: d
-- n'th member
-- an = a0 + n*d
ap : ℕ → ℕ → ℕ → ℕ
ap = λ a0 d n → {!!}

isZero : ℕ → Bool
isZero = λ n → {!!}

_-_ : ℕ → ℕ → ℕ
_-_ = {!!}

_eq_ : ℕ → ℕ → Bool
_eq_ = {!!}

_≥_ : ℕ → ℕ → Bool
_≥_ = {!!}

_>_ : ℕ → ℕ → Bool
_>_ = {!!}




---------------------------------------------------------
-- Descartes product
---------------------------------------------------------

-- define all the elements of Bool × Bool!

p1 p2 p3 p4 p5 : Bool × Bool
p1 = true , true
p2 = true , false
p3 = false , true
p4 = false , false

p5 = {!!}

uncurryBool : (Bool → Bool → Bool) → Bool × Bool → Bool
uncurryBool = {!!}

swapBool : Bool × Bool → Bool × Bool
-- swap (u , v) = (v , u) for any u, b
swapBool = {!!}

apply : (Bool → Bool) × Bool → Bool
-- apply (f , u) = f u
apply = {!!}



---------------------------------------------------------
-- Abstract types
---------------------------------------------------------

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a


idX     : X → X
idX = {!!}

pick    : X → X → X
pick = {!!}

pick'    : X → X → X
pick' = {!!}

f : pick ≡ pick'
f = {!!}

pick*   : X → (X → X) → X
pick* = {!!}

pick?   : (X → X) → X
pick? = {!!}

swap    : X × Y → Y × X
swap = {!!}

curry   : (X × Y → Z) → (X → Y → Z)
curry = {!!}

uncurry : (X → Y → Z) → (X × Y → Z)
uncurry = {!!}

assoc   : (X × Y) × Z → X × (Y × Z)
assoc = {!!}

diag    : X → X × X
diag = {!!}

_∘_     : (Y → Z) → (X → Y) → (X → Z)
_∘_ = {!!}
