module hf05-part1 where

open import Lib
open import Lib.Containers.Vector hiding (take; drop; replicate; splitAt; _[_]%=_; _[_]≔_)

{-
infixl 50 _!
_! : ℕ → ℕ
zero ! = 1
suc n ! = n ! * suc n
-}

{-
Definiáld a maximum függvényt, amely egy természetes számokat tartalmlazó
nem üres vektornak megadja a maximum elemét.

Segítség: Nem kell félni segédfüggvények definiálásától.
-}
maximum : {n : ℕ} → Vec ℕ ? → ℕ
maximum = ?

-- minimum-ot hasonlóan lehet definiálni.

maximum-test1 : maximum (1 ∷ 4 ∷ 2 ∷ 10 ∷ 90 ∷ []) ≡ 90
maximum-test1 = refl

maximum-test2 : maximum (100 ∷ 4 ∷ 2 ∷ 10 ∷ 90 ∷ []) ≡ 100
maximum-test2 = refl

maximum-test3 : maximum (1 ∷ 4 ∷ 200 ∷ 10 ∷ 90 ∷ 35 ∷ 65 ∷ []) ≡ 200
maximum-test3 = refl

{-
Definiáld az iteVec függvényt, amely legyen a vektor destruktora,
azaz feldolgozza egy vektor összes elemét.
(Ugyanazt csinálja, mint az iteList.)
-}
iteVec : {A B : Set}{n : ℕ} → (A → B → B) → B → Vec A ? → B
iteVec = ?

iteVec-test1 : iteVec _+_ 0 [] ≡ 0
iteVec-test1 = refl

iteVec-test2 : iteVec _+_ 0 (1 ∷ 5 ∷ 6 ∷ []) ≡ 12
iteVec-test2 = refl

iteVec-test3 : iteVec _*_ 1 (2 ∷ 5 ∷ 6 ∷ 10 ∷ []) ≡ 600
iteVec-test3 = refl

{-
Definiáld az elimVecᵣ és elimVecₗ függvényeket!
Az elimVecᵣ úgy működik, mint a foldr (iteVec).
Az elimVecₗ úgy működik, mint a foldl, tehát balról bontja le a vektort.
Ez a két függvény a foldr és foldl függőtípusos változatai, általánosabb,
így egyértelmű, hogy a függvénynek tényleg azt kell csinálni, mint a foldr-nek
és foldl-nek és más nem igazán lehet.
-}
elimVecᵣ : {A : Set}{n : ℕ}(B : ℕ → Set) → ({n : ℕ} → A → B ? → B ?) → B ? → Vec A ? → B ?
elimVecᵣ = ?

elimVecₗ : {A : Set}{n : ℕ}(B : ℕ → Set) → ({n : ℕ} → B ? → A → B ?) → B ? → Vec A ? → B ?
elimVecₗ = ?

elimVecᵣ-test1 : elimVecᵣ (λ _ → ℕ) _+_ 0 [] ≡ 0
elimVecᵣ-test1 = refl

elimVecᵣ-test2 : elimVecᵣ (λ _ → ℕ) _+_ 0 (1 ∷ 5 ∷ 6 ∷ []) ≡ 12
elimVecᵣ-test2 = refl

elimVecᵣ-test3 : elimVecᵣ (λ _ → ℕ) _*_ 1 (2 ∷ 5 ∷ 6 ∷ 10 ∷ []) ≡ 600
elimVecᵣ-test3 = refl

elimVecᵣ-test4 : elimVecᵣ (Vec ℕ) _∷_ [] (2 ∷ 5 ∷ 6 ∷ 10 ∷ []) ≡ (2 ∷ 5 ∷ 6 ∷ 10 ∷ [])
elimVecᵣ-test4 = refl

elimVecₗ-test1 : elimVecₗ (λ _ → ℕ) _+_ 0 [] ≡ 0
elimVecₗ-test1 = refl

elimVecₗ-test2 : elimVecₗ (λ _ → ℕ) _+_ 0 (1 ∷ 5 ∷ 6 ∷ []) ≡ 12
elimVecₗ-test2 = refl

elimVecₗ-test3 : elimVecₗ (λ _ → ℕ) _*_ 1 (2 ∷ 5 ∷ 6 ∷ 10 ∷ []) ≡ 600
elimVecₗ-test3 = refl

elimVecₗ-test4 : elimVecₗ (Vec ℕ) (λ acc x → x ∷ acc) [] (2 ∷ 5 ∷ 6 ∷ 10 ∷ []) ≡ (10 ∷ 6 ∷ 5 ∷ 2 ∷ [])
elimVecₗ-test4 = refl

{-
Definiáld a replicate függvényt, amely n db azonos elemet tesz bele
a vektorba.

Ahogy ebben az esetben is látható, az explicit paraméterek is elnevezhetők.
Pl. most n az első explicit paraméter.
-}
replicate : {A : Set}(n : ℕ) → A → Vec A ?
replicate = ?

replicate-test1 : {A : Set} → (λ (x : A) → replicate 5 x) ≡ (λ x → x ∷ x ∷ x ∷ x ∷ x ∷ [])
replicate-test1 = refl

replicate-test2 : replicate 3 true ≡ true ∷ true ∷ true ∷ []
replicate-test2 = refl

replicate-test3 : replicate 0 ≡ (λ (x : Bool) → [])
replicate-test3 = refl

{-
Definiáld a take függvény, amely n db elemet megtart a vektor elejéről.
A helyzet érdekessége, hogy most le is tudjuk írni, hogy van is legalább n db elem.
És nem is tudunk nagyobb számot megadni, mint ahány elemű a vektor.
-}
take : {A : Set}{m : ℕ} → (n : ℕ) → Vec A ? → Vec A ?
take = ?

take-test1 : take {ℕ} 4 (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
take-test1 = refl

take-test2 : (λ (xs : Vec Bool 10) → take {Bool} {10} 0 xs) ≡ (λ xs → [])
take-test2 = refl

take-test3 : take 3 (true ∷ false ∷ false ∷ true ∷ []) ≡ true ∷ false ∷ false ∷ []
take-test3 = refl

{-
Definiáld a drop függvényt, amely n db elemet elhagy a vektor elejéről.
-}
drop : {A : Set}{m : ℕ} → ? → Vec A ? → Vec A ?
drop = ?

drop-test1 : drop {ℕ} 0 [] ≡ []
drop-test1 = refl

drop-test2 : (λ (xs : Vec ℕ 10) → drop {ℕ} {10} 0 xs) ≡ (λ xs → xs)
drop-test2 = refl

drop-test3 : drop 2 (true ∷ false ∷ true ∷ []) ≡ true ∷ []
drop-test3 = refl

drop-test4 : drop 3 (true ∷ false ∷ true ∷ []) ≡ []
drop-test4 = refl

{-
Definiáld a zipWith függvényt, amely azonos elemszámú vektorokat összepárosít egy adott
függvény alapján (egyszerre haladva a két vektoron az elemeken alkalmazz egy függvényt).
-}
zipWith : {A B C : Set}{n : ℕ} → (A → B → C) → Vec A ? → Vec B ? → Vec C ?
zipWith = ?

zipWith-test1 : zipWith _+_ (1 ∷ 3 ∷ 9 ∷ 2 ∷ []) (10 ∷ 0 ∷ 5 ∷ 6 ∷ []) ≡ 11 ∷ 3 ∷ 14 ∷ 8 ∷ []
zipWith-test1 = refl

zipWith-test2 : zipWith _*_ (3 ∷ 9 ∷ 2 ∷ []) (10 ∷ 5 ∷ 6 ∷ []) ≡ 30 ∷ 45 ∷ 12 ∷ []
zipWith-test2 = refl

{-
Definiáld a restrictWith függvényt, amely hasonlóan működik,
mint a zipWith függvény azzal az egy különbséggel,
hogy a két vektor nem feltétlenül azonos elemszámú.
A rövidebb hosszáig működik a függvény.
Hogy melyikben van több elem, ezt nem tudjuk, bármelyik lehet a nagyobb
elemszámú.
-}

restrictWith : {A B C : Set}{n m : ℕ} → (A → B → C) → Vec A ? → Vec B ? → Vec C ?
restrictWith = ?

restrictWith-test1 : restrictWith _+_ (1 ∷ 3 ∷ 9 ∷ 2 ∷ []) (10 ∷ 0 ∷ 5 ∷ 6 ∷ []) ≡ 11 ∷ 3 ∷ 14 ∷ 8 ∷ []
restrictWith-test1 = refl

restrictWith-test2 : restrictWith _*_ (3 ∷ 9 ∷ 2 ∷ []) (10 ∷ 5 ∷ 6 ∷ []) ≡ 30 ∷ 45 ∷ 12 ∷ []
restrictWith-test2 = refl

restrictWith-test3 : restrictWith _+_ (3 ∷ 2 ∷ []) (10 ∷ 0 ∷ 5 ∷ 6 ∷ []) ≡ 13 ∷ 2 ∷ []
restrictWith-test3 = refl

restrictWith-test4 : restrictWith _*_ (3 ∷ 9 ∷ 2 ∷ 0 ∷ 1 ∷ 6 ∷ 10 ∷ []) (10 ∷ 5 ∷ 6 ∷ []) ≡ 30 ∷ 45 ∷ 12 ∷ []
restrictWith-test4 = refl
{-
Definiáld a splitAt függvényt, amely az n. indexű elemnél ketté bontja a vektort.
-}
splitAt : {A : Set}{m : ℕ} → ? → Vec A ? → ?
splitAt = ?

splitAt-test1 : {A : Set} → (λ (xs : Vec A 10) → splitAt {A} {10} 0 xs) ≡ (λ xs → [] , xs)
splitAt-test1 = refl

splitAt-test2 : splitAt {ℕ} 2 (1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ [] , [])
splitAt-test2 = refl

splitAt-test3 : splitAt {ℕ} 3 (1 ∷ 2 ∷ 3 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [] , [])
splitAt-test3 = refl

splitAt-test4 : splitAt {ℕ} 3 (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [] , (4 ∷ []))
splitAt-test4 = refl

{-
Definiáld a matrixAdd függvényt, amely a mátrix összeadást valósítja meg.
Segítség: A két mátrixnak milyennek kell lennie, hogy össze lehessen adni azokat?
-}
matrixAdd : {n m : ℕ} → Vec ? ? → Vec ? ? → Vec ? ?
matrixAdd = ?

matrixAdd-test1 : matrixAdd {10} [] [] ≡ []
matrixAdd-test1 = refl

matrixAdd-test2 : matrixAdd ([] ∷ [] ∷ []) ([] ∷ [] ∷ []) ≡ ([] ∷ [] ∷ [])
matrixAdd-test2 = refl

matrixAdd-test3 : matrixAdd
  ((1 ∷ 2 ∷ 3 ∷ []) ∷ (4 ∷ 5 ∷ 6 ∷ []) ∷ (1 ∷ 2 ∷ 3 ∷ []) ∷ (4 ∷ 5 ∷ 6 ∷ []) ∷ [])
  ((7 ∷ 0 ∷ 3 ∷ []) ∷ (5 ∷ 5 ∷ 6 ∷ []) ∷ (9 ∷ 1 ∷ 5 ∷ []) ∷ (4 ∷ 5 ∷ 6 ∷ []) ∷ [])
  ≡
  (8 ∷ 2 ∷ 6 ∷ []) ∷ (9 ∷ 10 ∷ 12 ∷ []) ∷ (10 ∷ 3 ∷ 8 ∷ []) ∷ (8 ∷ 10 ∷ 12 ∷ []) ∷ []
matrixAdd-test3 = refl