module en.hf07 where

open import Lib

{-
-- These functions are available in Lib under these names, so you can use them without any worries!

contradiction : ∀{i j}{P : Set i}{Whatever : Set j} → P → ¬ P → Whatever
contradiction p ¬p = exfalso (¬p p)

contraposition : ∀{i j}{P : Set i}{Q : Set j} → (P → Q) → ¬ Q → ¬ P
contraposition f ¬q p = contradiction (f p) ¬q

weaken : {X : Set} → X → ¬ ¬ X
weaken x = λ ¬x → ¬x x
-}

----------------------------------------------
-- Theory -- Formalization
----------------------------------------------

module F1 where

  -- If I go to work, then I get paid.
  form1 : Set
  form1 = {!!}

  -- If I get paid and I did not stay home, then I went to work.
  form2 : Set
  form2 = {!!}

  -- I went to work and I did not stay home.
  form3 : Set
  form3 = {!!}

  -- I get paid.
  K : Set
  K = {!!}

  -- Write down, then prove or disprove, that the first three statements imply K.
  proofK : Dec {lzero} {!!}
  proofK = {!!}

----------------------------------------------
-- Remaining Practice + e9, e10, f4' new
----------------------------------------------

-- It was covered in class, no problem, repetition is the father of learning.

dm2 : {X Y : Set} → ¬ X ⊎ ¬ Y → ¬ (X × Y)
dm2 (inl a) x₁ = a (fst x₁)
dm2 (inr b) x₁ = b (snd x₁)

dm2b : {X Y : Set} → ¬ ¬ (¬ (X × Y) → ¬ X ⊎ ¬ Y)
dm2b x = x (λ x₁ → inl (λ x₂ → x (λ x₃ → inr (λ y → x₃ (x₂ , y)))))

nocontra : {X : Set} → ¬ (X ↔ ¬ X)
nocontra (fst₁ , snd₁) = fst₁ (snd₁ (λ x → fst₁ x x)) (snd₁ (λ x → fst₁ x x))

¬¬invol₁ : {X : Set} → ¬ ¬ ¬ ¬ X ↔ ¬ ¬ X
fst ¬¬invol₁ = λ x x₁ → x λ x₂ → x₂ x₁
snd ¬¬invol₁ = λ x x₁ → x₁ x

¬¬invol₂ : {X : Set} → ¬ ¬ ¬ X ↔ ¬ X
fst ¬¬invol₂ = λ x x₁ → x (λ x₂ → x₂ x₁)
snd ¬¬invol₂ = λ x x₁ → x₁ x

nndnp : {X : Set} → ¬ ¬ (¬ ¬ X → X)
nndnp x = x (λ x₁ → exfalso (x₁ (λ x₂ → x (λ x₃ → x₂)))) 

dec2stab : {X : Set} → (X ⊎ ¬ X) → (¬ ¬ X → X)
dec2stab (inl a) x₁ = a
dec2stab (inr b) x₁ = exfalso (x₁ b)

-- This import provides the yes/no patterns. It's worth using with Dec.
-- Once decided, the line must start with yes if it's fulfilled. (This is the synonym of inl.)
-- If decided that it's not fulfilled, the line must start with no. (This is the synonym of inr.)

-- open import Lib.Dec.PatternSynonym

e3 : {X : Set} → Dec (¬ (X → (¬ X → X)))
e3 = inr (λ x → x (λ x₁ x₂ → x₁))

e4 : Dec ℕ
e4 = inl zero

e5 : Dec ⊥
e5 = inr exfalso

e6 : {X : Set} → Dec (⊥ → X ⊎ ¬ X)
e6 = inl exfalso 

e7 : {X : Set} → Dec (X × ¬ X → ¬ X ⊎ X)
e7 = inl λ x → inr (fst x)

e8 : {X : Set} → Dec ((X → X) → ⊥)
e8 = inr (λ x → x (λ x₁ → x₁))

e9 : {X Y : Set} → Dec (¬ (X ⊎ Y ↔ (¬ X → Y)))
e9 = inr (λ x → x ((λ x₁ x₂ → case x₁ (λ x₃ → exfalso (x₂ x₃)) (λ x₃ → x₃)) , (λ x₁ → inr (x₁ {!   !})))) 

e10 : {X Y : Set} → Dec (¬ ((¬ X → ¬ Y) → Y → X))
e10 {X} {Y} = inr λ x → x (λ x₁ x₂ → exfalso (x₁ (λ x₃ → x (λ _ _ → x₃)) x₂)) --λ x → x (λ x₁ x₂ → exfalso (x₁ (λ x₃ → x₁ (exfalso (x {!   !})) x₂) x₂))

f1 : {X Y : Set} → ¬ ¬ X ⊎ ¬ ¬ Y → ¬ ¬ (X ⊎ Y)
f1 x x₁ = (case x (λ x₂ → x₁ (inl (exfalso (x₂ (λ x₃ → x₁ (inl x₃)))))) λ x₂ → x₂ (λ x₃ → x₁ (inr x₃)))

f2 : ({X Y : Set} → ¬ (X × Y) → ¬ X ⊎ ¬ Y) → {X Y : Set} → ¬ ¬ (X ⊎ Y) → ¬ ¬ X ⊎ ¬ ¬ Y
f2 x x₁ = x (λ x₂ → x₁ (λ x₃ → case x₃ (λ x₄ → fst x₂ x₄) (λ x₄ → snd x₂ x₄))) 


-- EXAMPLES OF Dec LOOK LIKE THIS!

{-
Given the following logical statement, you have to decide whether it is fulfilled or not.

f3 : Dec ((X Y : Set) → X ⊎ Y → Y)
f3 = ?

How can this be checked?
Generally, the statement is still zeroth-order, the part after (: Set) is the statement.
In the zeroth order case, the simplest is to check the statement with the known truth table to see if it is fulfilled
 (we know from logic that the syntax and semantics are correct and complete).
Note: The only trap is the already seen X ⊎ ¬ X or ¬ ¬ X → X type of statements, which cannot be proven constructively, 
even though the table will show that they are true. Then these can be proven with double negation.

The following table can be prepared for the above statement:
The first columns are the letters appearing before (: Set), propositional variables, then all the substatements (the statements separated by arrows).
Then at the very end, put the complete statement, from which it's simpler to decide whether our statement is fulfilled, and if not fulfilled, then it's simple to decide from that when it does not.

| X | Y | X ⊎ Y | X ⊎ Y → Y
|---|---|-------|----------
| i | i |   i   | i ⊃ i = i
|---|---|-------|----------
| i | h |   i   | i ⊃ h = h
|---|---|-------|----------
| h | i |   i   | h ⊃ i = i
|---|---|-------|----------
| h | h |   h   | h ⊃ h = i

The implication operation needs to be accustomed to how it works; it's only false when the beginning of the statement is true, but the end is false.
From the last column of the table, we can see that there will be a point where the statement is not fulfilled.
For this investigation, ALWAYS look at the complete statement, so the suggested method is based on looking at the last column.

In class, we discussed that falsehood is encoded by 0-element types, and truth by at least 1-element types.
Any type can be used, Fin 0 is good for false, 0 ≡ 1 is good for false, Fin 1 is good for true, Bool is good for true, ℕ is good for true.
However, I recommend using ⊤ for encoding truth and ⊥ for encoding falsehood.

Let's convert the table based on this. The same table, just mark i and h with ⊤ and ⊥ instead.
(Note: Hereafter, I will only write down zeroth-order statements like this.)

| X | Y | X ⊎ Y | X ⊎ Y → Y
|---|---|-------|----------
| ⊤ | ⊤ |   ⊤   |     ⊤
|---|---|-------|----------
| ⊤ | ⊥ |   ⊤   |     ⊥
|---|---|-------|----------
| ⊥ | ⊤ |   ⊤   |     ⊤
|---|---|-------|----------
| ⊥ | ⊥ |   ⊥   |     ⊤

Then X and Y denote the specific types, while the other columns indicate whether the statement written there can be proven.

We see that there is a row where the complete statement is not fulfilled (this is the 2nd row).
Thus, we decided that the statement is not always fulfilled (not tautological), then we must provide that interpretation.


f3 : Dec ((X Y : Set) → X ⊎ Y → Y)
f3 = inr ?

The ? place should be given a value of type ((X Y : Set) → X ⊎ Y → Y) → ⊥.
                                   ^ Because of this arrow, we know that it's just a function, we can take it up as a hypothesis (logic calls this the deduction theorem).

f3 : Dec ((X Y : Set) → X ⊎ Y → Y)
f3 = inr (λ f → ?)

f : (X Y : Set) → X ⊎ Y → Y

Now, a value of type ⊥ must be produced at the ? place, essentially the task asks us to show when the statement is not fulfilled.
In this case, there's nothing else to do but look at the table, choose a row where the statement is not fulfilled (in other examples there might be multiple places where it does not hold, but it's completely irrelevant which one you choose),
then pass the corresponding values of that row directly to the f function.

Let's look at the 2nd row, we see that in the case of X = ⊤, Y = ⊥ the statement does not work. We just have to pass these types in this order to the f function.

f3 : Dec ((X Y : Set) → X ⊎ Y → Y)
f3 = inr (λ f → f ⊤ ⊥ ?)

Then at the ? place, we just have to prove that ⊤ ⊎ ⊥ can be proven. Of course, yes, inl tt solves it.
-}

f3 : Dec ((X Y : Set) → X ⊎ Y → Y)
f3 = inr (λ f → f ⊤ ⊥ (inl tt))

-- And the proof is complete.
{-
Of course, it's much faster to figure this out through simple THINKING. In the case of refutation, we always get the complete statement and ⊥ has to be produced from it.
At a glance, we know that only the adopted statement can return ⊥ in 100% of cases (this is always true), and in this specific case, ⊥ can only be the result if Y = ⊥.
Thus, cases where Y = ⊤ don't even need to be looked at, they are completely unnecessary. Instead of 4 cases, only 2 need to be examined, X = ⊤ and X = ⊥, to see if something special happens.
-}

{-

Let's look at another example:

f5 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f5 = ?

The same method as before, table:
(The function has X Y Z in that order, so we take them up in the same way.)

| X | Y | Z | (X → Z) × (Y → Z) | X × Y → Z | (X → Z) × (Y → Z) → (X × Y → Z)
|---|---|---|-------------------|-----------|--------------------------------
| ⊤ | ⊤ | ⊤ |         ⊤         |    ⊤      |               ⊤
|---|---|---|-------------------|-----------|--------------------------------
| ⊤ | ⊤ | ⊥ |         ⊥         |    ⊥      |               ⊤
|---|---|---|-------------------|-----------|--------------------------------
| ⊤ | ⊥ | ⊤ |         ⊤         |    ⊤      |               ⊤
|---|---|---|-------------------|-----------|--------------------------------
| ⊤ | ⊥ | ⊥ |         ⊥         |    ⊤      |               ⊤
|---|---|---|-------------------|-----------|--------------------------------
| ⊥ | ⊤ | ⊤ |         ⊤         |    ⊤      |               ⊤
|---|---|---|-------------------|-----------|--------------------------------
| ⊥ | ⊤ | ⊥ |         ⊥         |    ⊤      |               ⊤
|---|---|---|-------------------|-----------|--------------------------------
| ⊥ | ⊥ | ⊤ |         ⊤         |    ⊤      |               ⊤
|---|---|---|-------------------|-----------|--------------------------------
| ⊥ | ⊥ | ⊥ |         ⊤         |    ⊤      |               ⊤

We see that the last column only contains truths, so the statement is fulfilled.

f5 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f5 = inl ?

Then we need to prove that the statement works for every X, Y, Z, so we must provide a value of the type, define the function.
So, a value of type (X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z) is needed at the ? place.

How many parameters does the function we need to provide have? If we count, it comes out to be one less (this is always correct) than the number of columns in the table excluding the last.
In this case, we have 4 parameters (there will be one more soon), the X, Y, Z, and the (X → Z) × (Y → Z). During the proof, these propositional variables, i.e., the type variables,
are completely irrelevant and can't be used for anything.

f5 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f5 = inl (λ _ _ _ xzyz → ?)

Then, a value of type X × Y → Z is needed at the ? place. We see that a function must be returned as a result (or because of the deduction theorem in logic), so we write a lambda and pick up the remaining
1 parameter as well.

f5 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f5 = inl (λ _ _ _ xzyz → λ xy → ?)

I shorten this, as it means the same:

f5 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f5 = inl (λ _ _ _ xzyz xy → ?)

? at this place, we just need to provide a Z.
xzyz and xy are both ordered pairs, it's worth doing pattern matching on them. (It's worth doing pattern matching on anything that has a too specific type, thus has × or ⊎ in it.)

In the lambda, I showed two ways how to fit, now I choose one, of course the other one is possible too. Or you could even write a helper function for it.

f5 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f5 = inl (λ where _ _ _ (xz , yz) (x , y) → ?)

At this point, we can produce a Z in two ways, from the task's point of view it's completely irrelevant which one we choose.

One of them I write in a comment, the other as proper code.

f5 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f5 = inl (λ where _ _ _ (xz , yz) (x , y) → xz x)
-}

f5 : Dec ((X Y Z : Set) → (X → Z) × (Y → Z) → (X × Y → Z))
f5 = inl (λ where _ _ _ (xz , yz) (x , y) → yz y)

---------------------------------------------------------

f4 : Dec ((X Y Z : Set) → (X → Z) ⊎ (Y → Z) → (X ⊎ Y → Z))
f4 = inr (λ f → f ⊤ ⊥ ⊥ (inr exfalso) (inl tt))

f4' : Dec ((X Y Z : Set) → (X ⊎ Y → Z) → (X → Z) ⊎ (Y → Z))
f4' = inl (λ X Y Z x → inr (λ x₁ → x (inr x₁)))

nof6 : ¬ ((X Y Z : Set) → (X × Y → Z) → (X → Z) × (Y → Z))
nof6 x with x X Y Z p1 
    where 
        X Y Z : Set 
        X = ⊤ 
        Y = ⊥
        Z = ⊥
        p1 : X × Y → Z
        p1 (fst₁ , ())
... | fst₁ , snd₁ =   fst₁ tt

f6 : Dec ((X Y Z : Set) → (X × Y → Z) → (X → Z) × (Y → Z))
f6 = inr λ x → fst (x ⊤ ⊥ ⊥ λ {(t , ())}) tt --nof6

f7 : Dec ((X Y Z : Set) → (X ⊎ Y × Z) → (X ⊎ Y) × (X ⊎ Z))
f7 = inl (λ {X Y Z (inl a) → (inl a) , (inl a)
           ; X Y Z (inr b) → (inr (fst b)) , (inr (snd b))})

f8 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → ((X ⊎ Y) × Z))
f8 = inr (λ x → snd (x ⊤ ⊥ ⊥ ((inl tt) , (inl tt))))

f9 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → (X ⊎ Y × Z))
f9 = inl (λ {X Y Z (xz , inl a) → inl a
           ; X Y Z (inl a , inr b) → inl a
           ; X Y Z (inr b₁ , inr b) → inr (b₁ , b)})

f10 : Dec ((X Y Z : Set) → (X ⊎ Y) × (X ⊎ Z) → ((X ⊎ Y) × Z))
f10 = inr (λ x → snd (x ⊤ ⊥ ⊥ ((inl tt) , (inl tt)) ))

f11 : Dec ((P Q : Set) → (P → Q) × Q → P)
f11 = inr (λ x → x ⊥ ⊤ (exfalso , tt)) -- inl (λ P Q x → {!   !})

f12 : Dec ((A B : Set) → (A → B) → ¬ ¬ A → ¬ ¬ B)
f12 = inl (λ A B x x₁ x₂ → x₁ λ x₃ → x₂ (x x₃))

f13 : Dec ((P Q : Set) → (P → Q) → ¬ ¬ (¬ P ⊎ Q))
f13 = inl (λ P Q x x₁ → x₁ (inl (λ x₂ → x₁ (inr (x x₂)))))

f14 : Dec ((P Q : Set) → (P ↔ Q) → (¬ P × Q) ⊎ (P × ¬ Q))
f14 = inr λ x → case (x ⊥ ⊥ (exfalso , exfalso)) (λ x₁ → snd x₁) λ x₁ → fst x₁

f15 : Dec ((P Q R S : Set) → (P → Q) × (R → S) × (¬ P ⊎ S) → (Q ⊎ ¬ R))
f15 = inl (λ {P Q R S (p→q , r→s , nopors) → case nopors (λ x → inr (λ x₁ → x {!   !})) (λ x → inr (λ x₁ → {!   !}))})

f16 : Dec ((P Q : Set) → P × Q ↔ ((P → Q) ↔ P))
f16 = inl (λ P Q → (λ x → (λ x₁ → fst x) , (λ x₁ x₂ → snd x)) , (λ {(fst₁ , snd₁) → (fst₁ (λ x → snd₁ x x)) , (snd₁ (fst₁ (λ x → snd₁ x x)) (fst₁ (λ x → snd₁ x x)))}))

nof17 : ¬ ((P Q : Set) → (P → Q) ↔ ((P ⊎ ¬ Q) ↔ Q))
nof17 x with (fst (x P Q)) p1 
    where
        P Q : Set 
        P = ⊥
        Q = ⊥
        p1 : (P → Q)
        p1 = exfalso
        -- p2 : (P ⊎ ¬ Q) → Q
        -- p2 (inr b) = tt
... | fst₁ , snd₁ = fst₁ (inr exfalso)


f17 : Dec ((P Q : Set) → (P → Q) ↔ ((P ⊎ ¬ Q) ↔ Q))
f17 = inr nof17

nof18 : ¬ ((P Q : Set) → (¬ P ⊎ Q) ↔ P → P × ¬ Q )
nof18 x with x P Q p1
    where 
        P Q : Set 
        P = ⊤
        Q = ⊤
        p1 :  (¬ P ⊎ Q) ↔ P
        fst p1 x = tt
        snd p1 x = inr tt
... | fst₁ , snd₁ = snd₁ tt
f18 : Dec ((P Q : Set) → (¬ P ⊎ Q) ↔ P → P × ¬ Q)
f18 = inr nof18

-- It takes a lot of fussing around with this. A real proof!
-- Everything suggests itself, just for a long time.
f19 : {X Y : Set} → Dec (¬ ((X ↔ Y) ↔ (¬ X ↔ ¬ Y)))
f19 = {!   !}
      