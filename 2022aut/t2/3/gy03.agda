open import Agda.Builtin.Nat renaming (Nat to ℕ)

--TODO: I don't know whether it has too much of the material of the lecture

--data (like Haskell)

data Colour : Set where
  red green blue : Colour

colToℕ : Colour → ℕ
colToℕ col = {!!} --try C-c C-c!

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

-- this is an often-used operator
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

optone opttwo : ℕ ⊎ Colour --abbreviation
optone = inj₁ 0
opttwo = inj₂ red

retnum : ℕ ⊎ Colour → ℕ
retnum x = {!!} --try C-c C-c!

--record (rather like C-structs)

record Person : Set where
  field
    id : ℕ
    phone : ℕ

--open Person -- no need for 'Person.' before field names

bill : Person
Person.id bill = 12
Person.phone bill = 301234567

--this is like the Cartesius product
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_

point : ℕ × ℕ
point = {!!} --try C-c C-c here!

{-
_,_ : {A B : Set} → A → B → A × B
proj₁ (a , b) = {!!}
proj₂ (a , b) = {!!}
-}

point2 : ℕ × ℕ
point2 = 1 , 2

--the unit type: an empty record
record ⊤ : Set where

tt : ⊤
tt = record {}

--the empty type: an empty data
data ⊥ : Set where
