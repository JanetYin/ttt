open import lib hiding (_⊎_; inl; inr; case; ⊥; exfalso; _×_; fst; snd; _,_; ⊤; tt)

-- ez az eloadas 5 perccel rovidebb

{-
kviz:
(λ x → t) u = t[x↦u]  (β szabaly)

(λ x y → y) 2 =
(λ x → (λ y → y)) 2 =
(λ y → y)[x↦2] =
(λ y → y) =
(λ y → y)[x↦3] =
(λ x → (λ y → y)) 3 =
(λ x y → y) 3

λ x y → x = λ w v → w


t : A → B        u : A         
----------------------(1)      -----(2)
      t u : B                  1 : ℕ

u : ℕ    v : ℕ         x : A ⊢ t : B                    
--------------(3)    --------------------(4)            -------------------(5)
  u + v : ℕ          (λ x → t) : (A → B)                ...,x:A,...⊢ x : A
                                                                                               -----------------------(5)  ----------(2)
                                                                                               f:ℕ→ℕ,x:ℕ→ℕ ⊢ x : ℕ → ℕ     ...⊢3 : ℕ
                                                                           ---------(2)        --------------------------------------(1)
                                                                           ...⊢1 : ℕ           f:ℕ→ℕ,x:ℕ→ℕ ⊢ x 3 : ℕ
                                          -----------------------(5)       ----------------------------------------(3)
                                          f:ℕ→ℕ,x:ℕ→ℕ ⊢ f : ℕ → ℕ           f:ℕ→ℕ,x:ℕ→ℕ ⊢ (1 + x 3) : ℕ
 ----------------------------(5)      --------------------------------------------------------------------------(1)
 f:ℕ→ℕ,x:ℕ→ℕ ⊢ x : ℕ → ℕ              f:ℕ→ℕ,x:ℕ→ℕ ⊢ (f (1 + x 3)) : ℕ
 -----------------------------------------------------------------------------------(1)
                 f:ℕ→ℕ,x:ℕ→ℕ ⊢ (x (f (1 + x 3))) : ℕ
           -----------------------------------------------------(4)
            f:ℕ→ℕ ⊢ (λ x → x (f (1 + x 3))) : ((ℕ → ℕ) → ℕ)
           -----------------------------------------------------(4)
               λ f x → x (f (1 + x 3)) : (ℕ→ℕ) → (ℕ → ℕ) → ℕ

                ????
             ----------      -------(2)
              x:ℕ⊢x:ℕ→ℕ      x:ℕ⊢2:ℕ
 -------(2)   ---------------------(1)
 x:ℕ⊢3:ℕ      x:ℕ⊢x 2 : ℕ
 -----------------------(3)
 x:ℕ ⊢ 3 + x 2 : ℕ
------------------------(4)
λ x → 3 + x 2 : ℕ → ℕ



(1*2)+3     reszfaja     1*2                 λ
                                            / \
    +                     *                f   λ 
   / \                   / \                  / \
  *   3                 1   2                x  appl
 / \                                            / \
 1  2                                          x   appl
                                                    / \
                                                   f  +
                                                     / \
                                                     1  appl
                                                        / \
                                                       x   3
-}

-- → , (ℕ, Bool)

-- ⊎, CustRef, OrdNum, ugyanaz a szam; ∪ vs. ⊎

-- binaris osszeg tipus _+_, diszjunkt unio
data _⊎_ (A B : Set) : Set where   -- Either A B
  inl : A → A ⊎ B
  inr : B → A ⊎ B

-- (A ⊎ B) = vagy egy A, vagy egy B
-- A ∪ B
-- {0,1,2} ∪ {3,4,5} = {0,1,2,3,4,5} = {0,1,2} ⊎ {3,4,5}
-- {0,1,2} ∪ {2,3,4} = {0,1,2,3,4} ≠ {inl 0, inl 1, inl 2, inr 2, inr 3, inr 4} = {0,1,2} ⊎ {2,3,4}
-- {0} ∪ {0} = {0} ≠ {inl 0, inr 0} = 0 ⊎ 0

CustRef = ℕ
OrdNum  = ℕ

FormInput = CustRef ⊎ OrdNum
x y : FormInput
x = inl 1000
y = inr 1000

case : {A B C : Set} → (A → C) → (B → C) → A ⊎ B  → C
{-
case                   f         g        (inl a) = f a
case                   f         g        (inr b) = g b
-}
case f g (inl a) = f a
case f g (inr b) = g b

-- case (λ custref → ...) (λ ordnum → ...) x

-- ×, curry, uncurry, izomorfizmus

-- binaris szorzat tipus, par tipus, Descartes szorzat  -- Haskell: (A,B)
record _×_ (A B : Set) : Set where
  field
    fst : A
    snd : B
open _×_ public

_,_ : {A B : Set} → A → B → A × B  -- alahuzasok a parameterek helyet jelzi
fst (a , b) = a
snd (a , b) = b

-- ⊤, ⊥, Bool=⊤+⊤

-- nullaris szorzat tipus: ⊤ -- \top, egyelemu tipus, unit, void, ()
record ⊤ : Set where

tt : ⊤
tt = _ -- alahuzas azt jelzi, hogy Agda legyszi talald ki helyettem -- Haskellben tt helyett ()-t irnak

-- A tipus elemszamat jeloljuk ∣A∣-val.  ∣⊤∣=1 , ∣A∣=∣A∣,  ∣A×B∣ = ∣A∣*∣B∣,   ∣A×(B×C)∣ = ∣A∣*∣B∣*∣C∣, ...
-- a*1 = a           ∣A×⊤∣ = ∣A∣*∣⊤∣ = ∣A∣

-- ∣A⊎B∣ = ∣A∣ + ∣B∣
-- ∣A⊎⊥∣ = ∣A∣ + ∣⊥∣ = ∣A∣ + 0 = ∣A∣              --- \bot

data ⊥ : Set where -- bottom, ures tipus, (void)

exfalso : {A : Set} → ⊥ → A
exfalso () -- azt jeloli, hogy nincs eset

-- ⊤ ⊎ ⊥ ≅ ⊤  -- bijekcio, izomorfizmus

f : ⊤ ⊎ ⊥ → ⊤
f tb = tt

