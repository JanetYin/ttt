module 2021aut.t2.hf.people
  (Person    : Set)
  (Ann       : Person)
  (Kate      : Person)
  (Peter     : Person)
  (_childOf_ : Person → Person → Set)
  (_sameAs_  : Person → Person → Set) -- ez most itt az emberek egyenlosege
  where

open import lib

-- Define the _hasChild predicate.
_hasChild : Person → Set
x hasChild = Σ Person {!!}

-- Formalise: Ann is not a child of Kate.
ANK : Set
ANK = {!!}

-- Formalise: there is someone with exactly one child.
ONE : Set
ONE = Σ Person {!!}

-- Define the relation _parentOf_.
_parentOf_ : Person → Person → Set
-- use childOf
x parentOf y = {!!}

-- Formalise: No one is the parent of everyone.
NOPE : Set
NOPE = ¬ (Σ Person {!!})

-- Prove that if Ann has no children then Kate is not the child of Ann.
AK : ¬ (Σ Person λ y → y childOf Ann) → ¬ (Kate childOf Ann)
AK = {!!}

-- Prove that if there is no person who is his own parent than no one is the parent of everyone.
¬NOPE : ¬ (Σ Person λ x → x parentOf x) → NOPE
¬NOPE = {!!}

{- Solutions:
-- Define the _hasChild predicate.
_hasChild : Person → Set
x hasChild = Σ Person λ y → y childOf x

-- Formalise: Ann is not a child of Kate.
ANK : Set
ANK = ¬ (Ann childOf Kate)

-- Formalise: there is someone with exactly one child.
ONE : Set
ONE = Σ Person λ x → Σ Person λ y → y childOf x × ((z : Person) → z childOf x → z sameAs y)

-- Define the relation _parentOf_.
_parentOf_ : Person → Person → Set
x parentOf y = y childOf x

-- Formalise: No one is the parent of everyone.
NOPE : Set
NOPE = ¬ (Σ Person λ x → (y : Person) → x parentOf y)

-- Prove that if Ann has no children then Kate is not the child of Ann.
AK : ¬ (Σ Person λ y → y childOf Ann) → ¬ (Kate childOf Ann)
AK = λ w u → w (Kate , u)

-- Prove that if there is no person who is his own parent than no one is the parent of everyone.
¬NOPE : ¬ (Σ Person λ x → x parentOf x) → NOPE
¬NOPE = λ w u → w (π₁ u , π₂ u (π₁ u))
-}
