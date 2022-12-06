open import Agda.Builtin.Nat renaming (Nat to ℕ)

-- we need these from the previous file
infixl 5 _∘_ -- Function composition associates to the left  --\o
_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C   -- same as ... → (A → C)
f ∘ g = λ x → f (g x)

once : {A : Set} → (A → A) → A → A
once f = f

twice : {A : Set} → (A → A) → A → A
twice f = f ∘ f          --twice f x = f (f x)

-----------------------------------------------------------
-- theoretical questions
-----------------------------------------------------------

-- hint: the set variables in polymorphic functions were actually implicit parameters
-- how are implicit parameters marked in Agda?
-- how should an implicit parameter be passed explicitly?

-- how would you define an enumeration type in Agda?

-----------------------------------------------------------
-- coding tasks
-----------------------------------------------------------

-- write a power function that has two natural parameters n and k and returns nᵏ:
pow : ℕ → ℕ → ℕ
pow n k = {!!}

ex1 = twice (3 +_) 1
-- What is the type of ex1 ?
-- What is the value of ex1 ?

ex2 = twice twice (3 +_) 1
-- What is the type of ex2 ?
-- What is the value of ex2 ? why ?

-- what's wrong with the following code? correct it by adding or removing at most 5 characters
{-
eight : ℕ
eight = (2 +_) ∘ (3 *_) 2
-}

-- define a function that takes two parameters (it has to work with any type, even different ones) and returns the second one

-- define 𝔹 with data

-- what is the definition of ℕ?
