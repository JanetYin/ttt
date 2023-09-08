open import lib

-- meta

{-

halmazelmelet Zermelo Fraenkel, ZFC

elsőrendű logika, _∈_, {}, ZFC axiomai

  1 az egy halmaz
  ℕ az is egy halmaz
  1 ∈ ℕ egy állítás
  1 ∈ 2
  0 := {}                       0 := {}
  1 := {{{}},{}}                1 := {{}}
  2 := {{{{{}},{}}},{}}         2 := {{{}}}
  3 := {{{{{{{}},{}}},{}}},{}}  3 := {{{{}}}}
  ...

_:_      program : tipus

Mat11 :: *       Mat11 egy tipus
Mat : Int -> *
Mat 1 :: *
Mat (3^(2-n)) :: *
Mat 3 :: *

1 az egy program
ℕ az egy tipus
1 : ℕ az egy itelet, ez egy statikus informacio

Python        - Java
halmazelmelet - tipuselmelet

típuselmélet = type theory, Martin-Löf type theory 1970-es evek, cel: matematikai bizonyitasok leirasa, halmazelmelet helyett

70-80-as evek: De Bruijn, Automath

most: tipuselmeltre epulnek:
  Lean (amerikai, Kevin Buzzard), Agda (sved), Coq (francia), Idris (skot)
egyszeru tipuselmeltre epul: Isabelle/HOL
halmazelemtre epulo rendszer: Mizar

Google Chrome Coq-ban irt kodot

miert jo? 
-}

-- ℕ
-- A → B

{-

f : A → B

             +------------+
             |            | 
 a : A ----->|     f      |------> f a : B
             |            |
             +------------|

((f a) b) c
-}

add2' : ℕ → ℕ  -- add2 :: Int -> Int
add2' x = x + 2
--    ^:ℕ ^:ℕ

-- add2' 3 =(β redukcio)= 3 + 2 =(altalanos iskola)= 5

add2 : ℕ → ℕ
add2 = (λ x → x + 2)   -- Church

-- add2 3 =(rovidites)= (λ x → x + 2) 3 =(β redukcio)= 3 + 2 =(alt.isk) 5

plus : ℕ → (ℕ → ℕ)  -- curryzes
-- plus x y = x + y
-- plus = λ x → (λ y → x + y)
-- plus = λ x → λ y → x + y
plus = λ x y → x + y

k : (ℕ → ℕ) → ℕ
k  h =    h 2  + (h 3 + 1)
-- ^:ℕ→ℕ  \__/
--         :ℕ

n : ℕ
n = k add2
--  \/
--  : (ℕ → ℕ) → ℕ
--    \___/
--     : ℕ → ℕ
--  \____/
--   : ℕ

-- n = k add2 = add2 2 + (add2 3 + 1) = (2 + 2) + ((3 + 2) + 1) = 4 + 5 + 1 = 10

-- id :: a -> a
id : {A : Set} → A → A
id x = x

n' : ℕ
n' = id 3

-- polimorf fuggveny, implicit parameter  --- → jobbra zarojelezodik
_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C  -- (∘)
(g ∘ f) x = g (f x)
-- g : B → C
-- f : A → B
-- x : A
-- jobb oldal tipusa: C

square : ℕ → ℕ
square x = x * x

-- (square ∘ add2) 3 =(∘) square (add2 3) = square (2 + 3) = (2 + 3) * (2 + 3) =
-- 5 * 5 = 25
-- (add2 ∘ square) 3 = 11

-- id, ∘, polymorphism, square, (square ∘ add2) 3 β, ∘ is not commutative

{-

f : A → B
g : B → C

                          g ∘ f
             +-------------------------------+
             |                               | 
             |                               | 
             |                               | 
             |   +-----+           +-----+   | 
             |   |     |  f a : B  |     |   | 
    a : A ---+-->|  f  |---------->|  g  |---+--> g (f a) : C
             |   |     |           |     |   | 
             |   +-----+           +-----+   | 
             |                               | 
             |                               | 
             |                               |
             +-------------------------------+
-}

-- kovetkezo ora 4 perccel rovidebb
