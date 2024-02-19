-- quiz

open import Lib hiding (_∘_; id; _⊎_; case; _×_)

{-
(λ f x → f (f x x) (x + 1))
  x : ℕ
  f : ℕ → ℕ → ℕ
\________________________/
  : (ℕ → ℕ → ℕ) → ℕ → ℕ


(λ x → 1 + x) 3          /\
                        /  \
                       λ    3
                       /\
                      /  \
                     x    +
                         / \
                        /   \
                        1    x
term : Type

f : A → B     a : A
-------------------application, elimination rule of →
     f a : B

turnstyle ⊢ 

   x : A ⊢ b : B                                   b : A →
-------------------introduction rule for →      ---------------   λ : (A → B) → (A → B)
  λ x → b : A → B                               λ x → b : A → B

----------------------------    ----------------------------  ...
 x : A, y : B, z : C ⊢ x : A     x : A, y : B, z : C ⊢ y : B

                 n : ℕ  m : ℕ
-----    -----   ------------
1 : ℕ    2 : ℕ    n + m : ℕ

        ___A    _____b
   x   /   \   /     \   B
   f : ℕ → ℕ ⊢ f (f 2) : ℕ
   ---------------------------
   λ f → f (f 2) : (ℕ → ℕ) → ℕ
   λ x → b       : A       → B  

                 OK        OK
               --------   -----
               Γ⊢f:ℕ→ℕ→ℕ  Γ⊢x:ℕ     OK
               ----------------   -----
  OK                 Γ⊢f x:ℕ→ℕ    Γ⊢x:ℕ                    OK                 OK
-----------------    --------------------       --------------------    -----------
Γ ⊢ f : ℕ → ℕ → ℕ       Γ ⊢ f x x : ℕ             f : A, x : ℕ ⊢ x : ℕ    ... ⊢ 1 : ℕ
-----------------------------------------          -----------------------------
Γ:=________
/          \
f : ℕ→ℕ→ℕ, x : ℕ ⊢ f (f x x) : ℕ → ℕ          f : ℕ→ℕ→ℕ, x : ℕ ⊢ x + 1 : ℕ
---------------------------------------------------------------------------
f : ℕ→ℕ→ℕ, x : ℕ ⊢ f (f x x) (x + 1) : ℕ
----------------------------------------
f : ℕ→ℕ→ℕ ⊢ λ x → f (f x x) (x + 1) : ℕ → ℕ
----------------------------------------------------
 ⊢ (λ f → λ x → f (f x x) (x + 1)) : (ℕ→ℕ→ℕ) → ℕ → ℕ

not enough info:  λ x y → x + 1 : ℕ → A → ℕ


exercise for home: derive this:

------------------------------
λ f x → x (f (1 + x 3)) : ?


equational theory of Agda, conversion, reduction rules: how Agda programs run

------------------------
β : (λ x → b) a = b[x↦a]       (λ x → x + 3 * x) (1 + 1) = b[x↦a] = (1 + 1) + 3 * (1 + 1) = 8
                                      \_______/  \_____/
                                         b          a
-------------------------------
"numerical expression = result"

f : A → B
----------------------
η : f = λ x → f x

--------------------------------
α : (λ x → f) = (λ y → (f[x↦y]))

lim(1/(x+1)) = lim(1/(y+1)) = lim(1/(apple+1))    "bound names don't matter"n
x↦∞            y↦∞            apple↦∞         

int f(int x) { return (x + 1); } = int f(int apple) { return (apple + 1); }

(λ x → x + 1) = (λ y → y + 1) = (λ (v0 + 1))  "De Bruijn index"

(λ x → λ y → y + x) = λ (λ (v0 + v1))

  λ           λ
 / \          |
x   λ         λ
   / \        |
  y   +       +
     / \     / \
    y   x   v0  v1

shadowing:

λ x → λ x → x + 1        λ (λ v1)


lambda calculus
   ∧
typed lambda calulus (Gödel's System T)
   ∧
System F (Haskell)
   ∧
Martin-Löf type theory (Agda)

                                            WRONG
(λ x → (λ y → x + y)) y = (λ y → x + y)[x↦y] =  (λ y → y + y)
              ||
              ||========= (λ y → x + y)[x↦y] = (λ z → x + z)[x↦y]
              ||                                    ||
(λ x → (λ z → x + z)) y = (λ z → x + z)[x↦y] = (λ z → x + z)

-}

id' : {A : Set} → A → A  -- id' :: forall (a::*). a -> a
id' n = n

n : ℕ
n = id' 32

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) a = f (g a)

add2 square : ℕ → ℕ
add2 = λ x → x + 2
square = λ x → x * x
{-
(add2 ∘ square) 2 =(def ∘)
add2 (square 2) =(def add2)
(λ x → x + 2) (square 2) =(β)
(x+2)[x↦square 2] =
square 2 + 2 =(def square)
(λ x → x * x) 2 + 2 =(β)
(x*x)[x↦2] + 2 =
(2*2) + 2 = (math)
6
-}

-- sum types _⊎_  disjoint union,   {0,1,2}∪{0,3} = {0,1,2,3}   = Either
--                                  {0,1,2}⊎{0,3} = {inl 0,inl 1,inl 2,inr 0, inr 3}
data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

CustRef = ℕ
OrderNumber = ℕ

ComplaintNumber = CustRef ⊎ OrderNumber

-- labelled sums

case : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case f g (inl x) = f x
case f g (inr x) = g x

-- product types

record _×_ (A B : Set) : Set where
  field
    fst : A
    snd : B
open _×_

Four = Bool × Bool
one : Four
fst one = true
snd one = false

-- next lecture 1 minute shorter

-- sum, prod, (un)curry, (un)case
-- 0,1
-- Bool as 1+1
