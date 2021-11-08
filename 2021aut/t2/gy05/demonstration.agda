module 2021aut.t2.gy05.demonstration where
open import lib

--------------
-- Óra elején:

-- 17:45-17:50: Mindenki lépjen be Canvasba, kapcsolja be a gépét, stb.
--   A ZH-n két feladat lesz, két matematikai műveletet kell definiálni.
--   Ez most egyszerű és rövid is remélhetőleg annak, aki figyelt az órán.
--
-- 17:50-17:55: 1 feladatot meg lehet nézni a gyakorló feladatsorból
--   https://bitbucket.org/akaposi/ttt/src/master/2021aut/t2/gy03/exercise.agda
--
-- 17:55-18:00: ZH a canvasban
--   Ha valakinek technikai problémája akad, minél előbb küldje el nekem Teamsen a megoldást, AKÁR fotó formájában
--     (Lezsák Domonkos, lijjo8@inf.elte.hu)
--
-- A ZH megoldások benne vannak ebben a fájlban (első szekció)

---------------------------
-- Ismétlés az előző óráról

-- \bN, \Gl, \r

_+_ : ℕ → ℕ → ℕ
x + y = rec x (λ x → suc x) y
-- or shorter: _+_ = λ x → rec x suc

-- x * 3 = x + x + x
_*_ : ℕ → ℕ → ℕ
x * (suc y) = rec x (_+_ x) y
x * zero    = 0

-- Different approach:
-- x * 3 = 0 + x + x + x
_*'_ : ℕ → ℕ → ℕ
x *' y = rec 0 (λ x' → x' + x) y

-- Faktoriális
_! : ℕ → ℕ × ℕ
n ! = rec {Agda.Primitive.lzero} {ℕ × ℕ} {- Eredmény n=0 esetén:-}(1 , 0) {- Hogyan kapjuk meg a következő elemet:-}(λ (n-1! , n') → (n-1! * (suc n') , suc n')) {- Hányszor iterálunk:-}n

----------------------------------
-- Empty, unit, product, coproduct

----
-- Recap from the lecture

-- The empty type - no introduction
bot : ⊥ -- \bot
bot = _ -- this hole is impossible to solve

-- The unit type - trivial to introduce
top : ⊤ -- \top
top = triv

-- The product type (descartes-product) - holds both values (|A×B| = |A| * |B|)
times : 𝟚 × ℕ
times = (tt , 1)

--times, : 𝟚 × ⊥ -- |_| = 2
--times, = {!!}

-- The coproduct type - holds either the left or the right value (|A⊎B| = |A| + |B|)
uplus : 𝟚 ⊎ ℕ
uplus = ι₁ tt

uplus, : 𝟚 ⊎ ⊤
uplus, = ι₂ triv

-- The function type - transforms one value to the other (|A⇒B| ≥ |B| ^ |A|)
r : 𝟚 → ℕ
r = λ b → if b then 0 else 1

----
-- Putting C-c C-a to test

-- Try pressing C-c C-a in every hole, and check the result - these tasks are easy to solve

bot' : ⊥
bot' = _

top' : ⊤
top' = triv

times' : 𝟚 × ℕ
times' = tt , zero

uplus' : 𝟚 ⊎ ℕ
uplus' = ι₁ tt

r' : 𝟚 → ℕ
r' = λ x → zero

----
-- UTF-8

bot'' : {! \bot!} → ⊥
bot'' = λ bot → bot

top'' : {! \top!}
top'' = triv

times'' : {! _\times_!} ⊤ ⊤
times'' = (triv , triv)

uplus'' : {! _\uplus_!} ⊤ ⊥
uplus'' = {! \iota\_1!} triv

-- ok, skip r'', that's too easy...
r'' : {! 𝟚 \r ℕ!}
r'' = {! \Gl _ \r zero !}

----
-- Fun with unit / empty types

-- DON'T use C-c C-a here, only if you are stuck
-- These tasks are important to solve, ask me for more tasks if you need more exercise

task1 : ⊤
task1 = triv

task2 : ⊤ × ⊤
task2 = triv , triv

task3 : _×_ ⊤ ⊥
task3 = triv , {!!} -- well, this is impossible, skip this

task4 :   ⊥   → ⊤ × ⊥
task4 = λ bot → triv , bot -- it's possible

task5 : ⊤ × ⊥ → ⊥
task5 = λ (top , bot) → bot -- draw inspiration from task4

task6 : ⊥ ⊎ ⊤
task6 =  ι₂ triv -- only one (kind of) solution exists

task7 : ⊥ ⊎ ⊤ → ⊤ ⊎ ⊥
task7 = λ x → case x (λ bot → ι₁ triv)  λ top → ι₁ triv


--task7 = λ x → case x (λ bot → {!!}) (λ top → {!!})
-- There are multiple solutions for this task.
task7₁ task7₂ task7₃ : ⊥ ⊎ ⊤ → ⊤ ⊎ ⊥
-- First, technically you can define a (⊤ ⊎ ⊥) in every context
task7₁ = λ x → case x (λ bot → {! ι₁ triv!}) (λ top → {! ι₁ triv!})
-- But you can also make use our super-duper values extracted from the argument:
task7₂ = λ x → case x (λ bot → {! ι₂ bot!}) (λ top → {! ι₂ top!})
-- Note: This is kind of identical to using triv instead of top in the second case:
task7₃ = λ x → case x (λ bot → {! ι₂ bot!}) (λ top → {! ι₂ triv!})
-- (although task7₂ is much cooler 😎)
-- ... and you can mix these methods as you wish

-- using functions
task8 : (⊤ → ⊥) → ⊥
task8 = λ f → f triv -- given a hypothetical (f : ⊤ → ⊥) and (triv : ⊤) give me a ⊥

-- For task9, you don't have many different options - if you are stuck, ask the tutor for help
-- The where-notation means you can use f₁ and f₂ - useful while solving a more complex task
--   You DON'T HAVE TO understand the where notation, but I highly recommend spamming it everywhere
--     For further info and examples: https://agda.readthedocs.io/en/v2.6.2/language/let-and-where.html
task9 : {A : Set} → {B : Set} → (A → ⊥) × (B → ⊥) → A ⊎ B → ⊥
--task9 : (ℕ → ⊥) × (𝟚 → ⊥) → ℕ ⊎ 𝟚 → ⊥
{-
task9 x y = let
  f = π₁ x
  g = π₂ x
  in case y (λ a → f a) λ b → g b
  -}
{-
task9 x y = let
  pi1 = π₁ x
  pi2 = π₂ x
  in case y (λ left → pi1 left)  (λ right → pi2 right)
-}

task9 {A} {B} functions input = case input (λ a → (f₁ a)) (λ b → f₂ b)
  where
  f₁ : A → ⊥
  f₁ = π₁ functions
  f₂ : B → ⊥
  f₂ = π₂ functions
-- or using the λ-notation (you have to use let-in instead of where)
task9' : {A : Set} → {B : Set} → (A → ⊥) × (B → ⊥) → A ⊎ B → ⊥
task9' = λ functions input → let
  f₁ = π₁ functions
  f₂ = π₂ functions
  in case input (λ a → f₁ a) (λ b → f₂ b)

--------------
-- Equivalence

-- \lr = ↔

-- Two types are considered equivalent, if someone can convert from one to the other and vica versa.
-- For example let's map 𝟚 values as usual:
{- 𝟚 mapping:
false ≔ ff
true ≔ tt
-}
-- Also map ℕ values as known in C++:
{- ℕ mapping:
false ≔ zero
true ≔ suc x
-}

-- Conversion from and to can be defined with a pair of two functions: one from, and one to.
_↔'_ : Set → Set → Set
A ↔' B = (A → B) × (B → A)

{-
(T ⊎ (⊤ ⊎ ⊤)) ↔ (ℕ)
ι₁ triv      = 0
ι₂ (ι₁ triv) = 1
ι₂ (ι₂ triv) = 2
-}

isBijectionBetweenThem : (⊤ ⊎ (⊤ ⊎ ⊤)) ↔ (ℕ)
isBijectionBetweenThem = (
  λ x → case x ({-ι₁ triv-}λ x → 0) λ x →  case x (λ x₁ → {-t=ι₂ ι₁ triv-} 1 ) ( {-ι₂ ι₂ triv-}λ x₁ → 2 )
  ) , (
    λ n → rec ( ι₁ triv ) (λ uplus → ι₂ (case uplus (λ top → ι₁ triv) λ uplus' → case uplus' ({-ι₂ (ι₁ triv)-} λ top → ι₂ triv) ({-ι₂ (ι₂ triv)-} λ top → ι₂ triv))) n
  )

t→ℕ : (⊤ ⊎ (⊤ ⊎ ⊤)) → ℕ
t→ℕ = π₁ isBijectionBetweenThem

ℕ→t : ℕ → (⊤ ⊎ (⊤ ⊎ ⊤))
ℕ→t = π₂ isBijectionBetweenThem

nemCsinalSemmit : ℕ → ℕ
nemCsinalSemmit n = t→ℕ (ℕ→t n)

is1' : ℕ → 𝟚
is1' n = case t (λ x → ff) λ x → case x (λ x₁ → {-t=ι₂ ι₁ triv-} tt) λ x₁ → ff
  where
  t : ⊤ ⊎ (⊤ ⊎ ⊤)
  t = rec ( ι₁ triv ) (λ uplus → ι₂ (case uplus (λ top → ι₁ triv) λ uplus' → case uplus' ({-ι₂ (ι₁ triv)-} λ top → ι₂ triv) ({-ι₂ (ι₂ triv)-} λ top → ι₂ triv))) n

-- ↔ gets interesting when we play with top, bottom and type arguments: We don't have much choice
idl× : {A : Set} → ⊤ × A ↔ A
idl× =
  (λ x → π₂ x)
  ,
  (λ x → (triv , x))

-- Use C-c C-a, C-c C-r and C-c C-, extensively. Try writing `case x ? ?` whenever you have an idea
-- C-c C-, = info
-- C-c C-r = refine
-- C-c C-a = auto
dist : {A B C : Set} → A × (B ⊎ C) ↔ (A × B) ⊎ (A × C)
dist = (λ x → case (π₂ x) (λ z → ι₁ (π₁ x , z)) λ z → ι₂ (π₁ x , z)) , (λ x → (case x π₁ π₁) , (case x (λ z → ι₁ (π₂ z)) (λ z → ι₂ (π₂ z))))


------------------
-- Predicate logic
-- (extra info for the future - not important but juicy material)

-- Later on in the lecture we'll introduce the "predicate logic".
-- It enables us to do logic-business in the types.

-- 𝕃 ≔ Set
-- true ≔ ⊤
-- false ≔ ⊥
-- ∧ ≔ _×_
-- ∨ ≔ _⊎_
-- = ≔ ↔

-- A statement is a type, and it's true, if it has a definition.

-- For example, let's proof that (false ∧ true = false).
F∧T=F : ⊥ × ⊤ ↔ ⊥
F∧T=F = π₁ , (λ x → x , triv) -- C-c C-a works

-- The opposite doesn't hold
F∧T=T : ⊥ × ⊤ ↔ ⊤
F∧T=T = {!!} -- impossible
