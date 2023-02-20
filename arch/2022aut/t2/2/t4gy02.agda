open import Agda.Builtin.Nat renaming (Nat to ℕ)

--booleans:
data 𝔹 : Set where
  false true : 𝔹

if_then_else : {A : Set} → 𝔹 → A → A → A    --{A : Set} means A can be any Set
if true  then x else y = x
if false then x else y = y

aBool : 𝔹
aBool = true

bBool : 𝔹
bBool = false

cBool : 𝔹
cBool = if aBool then true else false

id𝔹' : 𝔹 → 𝔹
id𝔹' b = b

not : 𝔹 → 𝔹
not false = true
not true = false

-- Define the functions 'and' and 'or':
and : 𝔹 → 𝔹 → 𝔹
and false b2 = false
and true b2 = b2

or : 𝔹 → 𝔹 → 𝔹
or = {!!}

-- Define a function  add-or-mult : 𝔹 → ℕ → ℕ
--  such that  add-or-mult true n m = n + m   and   add-or-mult false n m = n * m  for every n, m : ℕ
add-or-mult : 𝔹 → ℕ → ℕ → ℕ
add-or-mult false n m = n * m
add-or-mult true n m = n + m

-- Define as many different functions of type  𝔹 → 𝔹  as you can:
f1 f2 f3 f4 f5 : 𝔹 → 𝔹
f1 = not
f2 = λ b → b
f3 = λ b → true
f4 = λ b → false
f5 = {!!}
-- How many exist?

-- Define as many different functions of type  𝔹 → 𝔹 → 𝔹  as you can:
g1 g2 g3 g4 g5 : 𝔹 → 𝔹 → 𝔹      --2 ^ (2 ^ 2)=16
g1 = and
g2 = or
g3 = {!!}
g4 = {!!}
g5 = {!!}
-- How many exist?


-- Define as many different functions of type  (𝔹 → 𝔹) → 𝔹  as you can:
h1 h2 h3 h4 h5 : (𝔹 → 𝔹) → 𝔹
h1 f = {!!}
h2 = {!!}
h3 = {!!}
h4 = {!!}
h5 = {!!}
-- How many exist?
{-
       not    consttrue      constfalse      id
        2   *     2       *       2       *   2
-}


-- NOTE: eddig jutottunk
--------------------------------------------------------------------------------

-- How many different functions are there of type  ((𝔹 → 𝔹) → 𝔹) → 𝔹 ?

-- Polymorphism
id : {A : Set} → A → A       -- A can be any Set (actually, it is a hidden parameter)
id = {!!}

idℕ : ℕ → ℕ
idℕ = id {ℕ}                  -- and it can be explicitly passed

id𝔹 : 𝔹 → 𝔹
id𝔹 = id                      -- but Agda can deduce it automatically

idℕ→ℕ : (ℕ → ℕ) → (ℕ → ℕ)
idℕ→ℕ = id                   -- same here

const : {A B : Set} → A → B → A  -- now two types
const = {!!}

infixl 5 _∘_ -- Function composition associates to the left
_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
_∘_ = {!!}

once : {A : Set} → (A → A) → A → A
once = {!!}

twice : {A : Set} → (A → A) → A → A
twice = {!!}

-- (3 +_) is a curried function, it adds 3 to its argument
-- (try it with C-c C-n)
ex1 = twice (3 +_) 1
-- What is the type of ex1 ?
-- What is the value of ex1 ?

ex2 = twice twice (3 +_) 1
-- What is the type of ex2 ?
-- What is the value of ex2 ? why ?

