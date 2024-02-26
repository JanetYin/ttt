module lec03 where

open import Lib hiding (_×_ ; fst ; snd ; Σ ; _,_ ; _+_ ; _*_ ; _^_ ; pred ; pred')
open import Lib.Product

{-
-- ×β
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

-- β-rule: how to compute a constructor applied to a destructor.
-- A : Set; B : Set
-- a : A, b : B
-- fst : A × B → A
fst (a , b) ≡ a
snd (a , b) ≡ b

-- ×η
-- η-rule: how to compute a destructor applied to a constructor
fst, snd

-- x : A × B
(fst x , snd x) ≡ x

-- | ⊤ | = 1
-- | ⊥ | = 0
-- | Bool | = 2
-- | ⊤ ⊎ ⊤ | = | ⊤ | + | ⊤ | = 1 + 1 = 2 -- inr tt; inl tt
-- | Bool × ⊤ | = | Bool | ∙ | ⊤ |       -- false , tt ; true , tt
-- | A → B |
--
-- ℕ ⊎ ℕ ≅ Bool × ℕ
-- | ℕ | + | ℕ | = 2 ∙ | ℕ |
-- Isomorphism: ∃(f : A → B) ∃(g : B → A) : f ∘ g = id AND g ∘ f = id
-- where id = λ x → x
-}

Bool' : Set
Bool' = ⊤ ⊎ ⊤

true' : Bool'
true' = inl tt

false' : Bool'
false' = inr tt

if_then_else''_ : {A : Set} → Bool' → A → A → A
if (inl tt) then x else'' y = x
if (inr tt) then x else'' y = y

f : ℕ ⊎ ℕ → Bool' × ℕ
f (inl a) = true' , a
f (inr b) = false' , b

g : Bool' × ℕ → ℕ ⊎ ℕ
g (b , n) = if b then inl n else'' inr n

-- HW: prove that ∀ x → f (g x) ≡ x
-- HW: prove that ∀ x → g (f x) ≡ x

-- Moses Schönfinkel
curry : {A B C : Set} → (A × B → C) → (A → B → C)
curry f a b = f (a , b)

uncurry : {A B C : Set} → (A → B → C) → A × B → C
uncurry f a×b = f (fst a×b) (snd a×b)

{-
-- f : A → B → C
curry (uncurry f) =(η-rule for functions (uncurry))
curry (λ ab → uncurry f ab) =(def uncurry)
curry (λ ab → f (fst ab) (snd ab)) =(η-rule for functions (curry))
λ a → curry (λ ab → f (fst ab) (snd ab)) a =(η-rule for functions (curry))
λ a b → curry (λ ab → f (fst ab) (snd ab)) a b =(def curry)
λ a b → (λ ab → f (fst ab) (snd ab)) (a , b) =(β-rule for functions)
λ a b → f (fst (a , b)) (snd (a , b)) =(×β₁)
λ a b → f a (snd (a , b)) =(×β₂)
λ a b → f a b =(η-rule for functions ×2)
f
-}
{-
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
-}
-- ℕ = {zero, suc (zero), suc (suc zero), ...}


-- WRONG
{-
double : ℕ → ℕ
double x = if x == 0 then 0 else suc (suc (double (x -' 1)))
-}
{--

x              ->        -'
                        /  \       ----> AST of expression is bigger, so it cannot detect it terminating.
                       x    1

-}

double : ℕ → ℕ
double zero    = zero
-- 2 * (1 + x) = 2 + 2 * x
double (suc x) = suc (suc (double x))
{-
suc
 |         ->   x        -----> Agda can determine that the function must terminate
 x
-}

half : ℕ → ℕ
half zero = 0
half (suc zero) = 0
-- (2 + x) / 2 == 1 + (x / 2)
half (suc (suc x)) = suc (half x)

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

_*_ : ℕ → ℕ → ℕ
zero * y = 0
-- ((1 + x) * y) == y + x * y
suc x * y = y + (x * y)

-- β-rule for ℕ
{-
zero : ℕ
suc : ℕ → ℕ
-}
iteℕ : {A : Set} → A → (A → A) → ℕ → A
iteℕ a f zero = a
iteℕ a f (suc n) = f (iteℕ a f n)

add : ℕ → ℕ → ℕ
add x y = iteℕ x suc y

{-
This is what we defined by the add function:
_+'_ : ℕ → ℕ → ℕ
x +' zero = x
x +' suc y = suc (x +' y)
-}
