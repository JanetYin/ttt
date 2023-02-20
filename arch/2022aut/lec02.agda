open import lib

-- a b c : ℕ
{-
ℕ → ℕ → ℕ = ℕ → (ℕ → ℕ)

-}

f : ℕ → ℕ
f = λ n → n

-- fuggveny tipus

add2 : ℕ → ℕ
-- add2 n = n + 2
add2 = (λ n → n + 2)

-- egyenlosegi erveles = program futasa agdaban
-- add2 3 = (λ n → n + 2) 3 = 

-- 1924 Moses Schonfinkel: S,K kombinatorok
-- Alonso Church (193x): λ kalkulus - bonyolultabb, konnyen olvashato, termeszetes
{-
   t ::= x | λ x → t | t t    t term, kifejezesek, program, szamitasi eljaras, 
   (λ x → t) t' = t[x↦t']   β, szamitas    helyettesites (* α-ekvivalencia, elfedes, fresh name convention, capture avoidance)
   t = (λ x → t x)  -- t : A → B   η, egyediseg
   (λ x → x + x) 3 = (x + x)[x ↦ 3] = 3 + 3  -- Church encoding (tiszta λ-kalkulusban szamok, osszeadas stb. elkodolasa)
   (λ x → (λ x → x + 3)) 2 =  (λ x → x + 3)[x ↦ 2] = (λ x → x + 3)    elfedes

   1
   ∫ 1/(x^2) dx          (λ x → x + 3)        { x^2 | x <- [0..10] }    lim (1/1+x)     int f(int x) {return (x+2);}       for (x = 1 to 3) {  y := y + x }
   0                                                                    x↦∞                               
     -------  ^             ^   -----           ---   ^                 ^   -------               ^   -------------             ^            -------------

   kotott valtozo neve nem szamit (alfa-ekvivalencia): (λ x → x + 3) = (λ y → y + 3)
             _____
    ________/__   \
   /       /   \   \
   \* → (λ * → * + *)

   (λ x → (λ y → x + y)) y =  (λ y → x + y)[x ↦ y] ≠ λ y → y + y
     ||
   (λ x → (λ z → x + z)) y = (λ z → x + z)[x ↦ y] = λ z → y + z


   t : A → B     u : A          t : B, es t-ben szerepelhet egy x : A tipusu valtozo
   -------------------          ----------------------------------------------------
      t u : B                              (λ x → t) : A → B

   (λ x → (λ x → x + 3)) 2 
                     ^ : ℕ            _+_ : ℕ → ℕ → ℕ     x : ℕ
                                      -------------------------         (A→B→C) = A→(B→C)
                 \___/                     _+_ x : ℕ → ℕ        3 : ℕ          (t u v) = (t u) v
                                           --------------------------          (λ x y → t) = λ x → λ y → t = λ x → (λ y → t)
                  : ℕ                           _+_ x 3 : ℕ     ebben van egy x : ℕ
                                                -----------------------------------
                                                   λ x → _+_ x 3 : ℕ → ℕ

          \___________/  ^:ℕ
            : ℕ → ℕ
    \____________________/
      : ℕ → ℕ
    
   (λ x → (λ x → x + 3)) : ℕ → ℕ → ℕ


   t : ℝ, es t-ben szerepelhet x : ℝ
   ---------------------------------
          b      
          ∫ t dx : ℝ
          a

    ∫ : (ℝ → ℝ) → ℝ

    b
    ∫ (λ x → t)
    a

λ a leheto legtovabb tart a λ torzse
-}
-- Alan Turing (193x+1): Turing gep

-- polimorf tipus

-- osszeg, szorzat tipus

{-
- add2, add2 3 kiszamitas
- λ verzio, kiszamitas
- curry: add, add 3 tipusa
- zarojelezes
- magasabbrendu fgv. k : (ℕ→ℕ)→ℕ, kiszamitas
-}
{-
id, kompozicio
- id
- implicit param
- kompozicio, infix
- square ∘ add2, kiszamitas, kompozicio nemkommutativ
-}

id : {A : Type} → A → A
id = λ a → a

idℕ : ℕ → ℕ
idℕ n = n

idBool : Bool → Bool
idBool b = b

harom : ℕ
-- harom = id 3 -- id 3 = (λ a → a) 3 = a[a↦3] = 3
harom = id {ℕ} 3

_∘_ : {A B C : Type} → (B → C) → (A → B) → A → C --- \o
f ∘ g = λ x → f (g x)
-- f(x)       x | f      f(x)

square : ℕ → ℕ
square n = n * n
{-
(square ∘ add2) 3 =
(λ x → square (add2 x)) 3 =
square (add2 3) =
square ((λ x → x + 2) 3) =
square (3 + 2) =
(λ n → n * n) (3 + 2) =
(λ n → n * n) 5 =
5 * 5 =
25
-}
