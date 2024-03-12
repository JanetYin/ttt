open import Lib

{-
(λ x → case x (λ y → true) (λ z → true))

w : A ⊎ B      l : A → C      r : B → C      x : A ⊢ t : B
---------------------------------------     ---------------
         case w l r : C                     λ x → t : A → B

                                 HW                        HW
---------------       ------------------------   ------------------------
x:A⊎B ⊢ x : A⊎B       x:A⊎B ⊢ λy→true : A→Bool   x:A⊎B ⊢ λz→true : B→Bool
-------------------------------------------------------------------------
x:A⊎B ⊢ case x (λ y → true) (λ z → true) : Bool
-----------------------------------------------------
(λ x → case x (λ y → true) (λ z → true)) : A⊎B → Bool


what can you write after data?

coinductive types

|A⊎B| = ∣A∣ + ∣B∣
∣A→B∣ = ∣B∣^∣A∣

∣⊤→Bool∣ = 2
∣Bool→⊥∣ = 0
∣ℕ→⊤∣ = 1

(a^b)^c = a^(b*c)      (b,c)->a  ≅  c->(b->a)
                       B × C → A ≅  B → C → A

types form a commutative exponentional rig
                                       semiring
                                       ring without negation
-}

-- inductive
data Tree3 : Set where
  node : Tree3 → Tree3 → Tree3 → Tree3
  leaf : Tree3

-- iteration = recursion = fold = catamorphism = nondependent eliminator

--         Tree3-algebra, Tree3-model, Tree3-structure
--         V
iteTree3 : (A : Set)(n : A → A → A → A)(l : A) -> Tree3 -> A
iteTree3 A n l (node t1 t2 t3) = n (iteTree3 A n l t1)
                                   (iteTree3 A n l t2)
                                   (iteTree3 A n l t3)
iteTree3 A n l leaf            = l
                                   
isLeaf : Tree3 -> Bool
isLeaf = iteTree3 Bool (λ _ _ _ → false) true

data T1 : Set where
  node : (ℕ → T1) → T1
  leaf : T1

t1 : ℕ → T1
t1 zero = leaf
t1 (suc n) = node (λ _ → t1 n)

t2 : T1
t2 = node (λ n → t1 n)
{- t2 looks like this:
    node 
   /   |           \           \
leaf  node         node        node
      ///|\\...    //|\\       |            ...
      leaf...     node...     node
                  //|\         |
                  leaf        node
                               |
                               leaf

there is no infinite branch in t2, but for any n:ℕ, there is a branch longer than n
-}

data T2 : Set where
  con : T2 → (T2 → T2)
-- this is the empty type
{-
       →
      /  \
     T2   →
         / \
        T2  T2
-}

{-# NO_POSITIVITY_CHECK #-}
data T3 : Set where      -- data T3 = Con (T3 -> T3)
  con : (T3 → T3) → T3
{-
       →
      /  \
     →   T3
    / \
   T3  T3
-}

app : T3 → T3 → T3
app (con f) x = f x

Ω : T3
Ω = con λ x → app x x

-- app Ω Ω = app (con λ x → app x x) Ω = (λ x → app x x) Ω = app Ω Ω

-- don't try to normalise app Ω Ω!

-- strictly positive constructors are the only ones allowed:
--   T cannot appear on the lhs of an arrow in the left hand children of an arrow

{-# NO_POSITIVITY_CHECK #-}
data Weird : Set where
  con : (Weird → ⊥) → Weird

fromWeird : Weird → (Weird → ⊥)
fromWeird (con f) = f

w : Weird
w = con λ w' → fromWeird w' w'

bot : ⊥
bot = fromWeird w w

-- T → (ℕ → T) → T

-- F X = 1 + 3*X + 5*X^2 + ...
-- F X = ⊤ ⊎ (⊤⊎⊤⊎⊤)×X ⊎ ....
-- data is the least fixpoint of such a polynomial,
-- A is a fixpoint of F if A ≅ F A
-- ℕ = least fixpoint of F where F X = ⊤ ⊎ X,   ℕ ≅ ⊤ ⊎ ℕ

-- coinductive types

-- ⊎ inductive
-- × coinductive 

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream public

-- Stream Bool = {true,false,true,false,...}
trues : Stream Bool
head trues = true
tail trues = trues

-- when you DESTRUCT  an elt of an DATATYPE,  you can   PATTERN MATCH on it
-- when you CONSTRUCT an elt of a CODATATYPE, you can COPATTERN MATCH

-- from 0 = {0,1,2,3,4,5,...}
from : ℕ → Stream ℕ
head (from i) = i
tail (from i) = from (i + 1)

-- try to normalise head (tail (tail (tail (from 100))))

genStream : {A : Set} → (B : Set) → (B → A) → (B → B) → B → Stream A
head (genStream B h t b) = h b
tail (genStream B h t b) = genStream B h t (t b)

-- HW: define from and trues using genStream

-- next class is 3 minutes shorter
