open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Bool renaming (Bool to 𝔹)

--TODO: I don't know whether it has too much of the material of the lecture

-- TODO: Type!
-- TODO: internal representation of ℕ (is it optimised?)

--data (like Haskell)

data Colour : Set where
  red green blue : Colour

colToℕ : Colour → ℕ
colToℕ red = 1
colToℕ green = 2
colToℕ blue = 3

-- NOTE: we were here --------------------------------------------------------------------------

{-
https://agda.readthedocs.io/en/v2.5.2/language/built-ins.html
The Agda type checker knows about, and has special treatment for, a number of different concepts. The most prominent is natural numbers, which has a special representation as Haskell integers and support for fast arithmetic. The surface syntax of these concepts are not fixed, however, so in order to use the special treatment of natural numbers (say) you define an appropriate data type and then bind that type to the natural number concept using a BUILTIN pragma.

Binding the built-in natural numbers as above has the following effects:

    The use of natural number literals is enabled. By default the type of a natural number literal will be Nat, but it can be overloaded to include other types as well.
    Closed natural numbers are represented as Haskell integers at compile-time.
    The compiler backends compile natural numbers to the appropriate number type in the target language.
    Enabled binding the built-in natural number functions described below.
-}

{-
Type was only an alias for Set in lib.agda; it does not mean anything more
-}

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

nt j3 j5 : Maybe ℕ
nt = nothing
j3 = just 3
j5 = just 5

mmn : Maybe (Maybe ℕ)
mmn = just (just 3)

-- this is an often-used operator
data _⊎_ (A B : Set) : Set where
  injl : A → A ⊎ B
  injr : B → A ⊎ B

optone opttwo : ℕ ⊎ Colour --abbreviation
optone = injl 0
opttwo = injr red

retnum : ℕ ⊎ Colour → Maybe Colour
retnum (injl n) = nothing
retnum (injr c) = just c

npn1 npn2 : ℕ ⊎ ℕ
npn1 = injl 4
npn2 = injr 4

nntobool : ℕ ⊎ ℕ → 𝔹
nntobool (injl _) = true
nntobool (injr _) = false

--record (rather like C-structs)

record Person : Set where
  field
    id : ℕ      -- Person → ℕ
    phone : ℕ   -- Person → ℕ

open Person -- no need for 'Person.' before field names
--like 'using'

bill : Person
id bill = 12
phone bill = 301234567

joe : Person
id joe = 20
phone joe = 307654321

--this is like the Cartesius product
--it's not in Haskell
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A   --proj₁
    snd : B   --proj₂

open _×_

point : ℕ × ℕ
point = {!!} --try C-c C-c here!

{-
-- that's what it generates
_,_ : {A B : Set} → A → B → A × B
fst (a , b) = a
snd (a , b) = b
-}

point2 : ℕ × ℕ
point2 = 1 , 2

--the unit type: an empty record
record ⊤ : Set where    --\top

tt : ⊤
tt = record {}

--the empty type: an empty data (no constructors ⇒ cannot construct an element)
data ⊥ : Set where
