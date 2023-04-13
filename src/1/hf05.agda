{-# OPTIONS --guardedness #-}
module hf05 where

open import lib

infixr 5 _∷_
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data Fin : ℕ → Set where  -- Fin n = n-elemu halmaz
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

length : {A : Set} → List A → ℕ
length [] = 0
length (_ ∷ xs) = suc (length xs)

map : {A B : Set}{n : ℕ} → (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_++_ : {A : Set}{m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 10 _!
_! : ℕ → ℕ
zero ! = 1
suc n ! = n ! * suc n

{-
Definiáld a maximum függvényt, amely egy természetes számokat tartalmlazó
nem üres vektornak megadja a maximum elemét.

Segítség: Nem kell félni segédfüggvények definiálásától.
-}
maximum : {n : ℕ} → Vec ℕ {!   !} → ℕ
maximum = {!   !}

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
iteVec : {A B : Set}{n : ℕ} → (A → B → B) → B → Vec A {!   !} → B
iteVec = {!   !}

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
elimVecᵣ : {A : Set}{n : ℕ}(B : ℕ → Set) → ({n : ℕ} → A → B {!   !} → B {!   !}) → B {!   !} → Vec A {!   !} → B {!   !}
elimVecᵣ = {!   !}

elimVecₗ : {A : Set}{n : ℕ}(B : ℕ → Set) → ({n : ℕ} → B {!   !} → A → B {!   !}) → B {!   !} → Vec A {!   !} → B {!   !}
elimVecₗ = {!   !}

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
-}
replicate : {A : Set}(n : ℕ) → A → Vec A {!   !}
replicate = {!   !}

replicate-test1 : {A : Set} → (λ (x : A) → replicate 5 x) ≡ (λ x → x ∷ x ∷ x ∷ x ∷ x ∷ [])
replicate-test1 = refl

replicate-test2 : replicate 3 true ≡ true ∷ true ∷ true ∷ []
replicate-test2 = refl

replicate-test3 : replicate 0 ≡ (λ (x : Bool) → [])
replicate-test3 = refl

{-
Definiáld a drop függvényt, amely n db elemet elhagy a vektor elejéről.
-}
drop : {A : Set}{m : ℕ} → {!   !} → Vec A {!   !} → Vec A {!   !}
drop = {!   !}

drop-test1 : drop {ℕ} 0 [] ≡ []
drop-test1 = refl

drop-test2 : (λ xs → drop {ℕ} {10} 0 xs) ≡ (λ xs → xs)
drop-test2 = refl

drop-test3 : drop 2 (true ∷ false ∷ true ∷ []) ≡ true ∷ []
drop-test3 = refl

drop-test4 : drop 3 (true ∷ false ∷ true ∷ []) ≡ []
drop-test4 = refl

{-
Definiáld a zipWith függvényt, amely azonos elemszámú vektorokat összepárosít egy adott
függvény alapján (egyszerre haladva a két vektoron az elemeken alkalmazz egy függvényt).
-}
zipWith : {A B C : Set}{n : ℕ} → (A → B → C) → Vec A {!   !} → Vec B {!   !} → Vec C {!   !}
zipWith = {!   !}

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

restrictWith : {A B C : Set}{n m : ℕ} → (A → B → C) → Vec A {!   !} → Vec B {!   !} → Vec C {!   !}
restrictWith = {!   !}

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
splitAt : {A : Set}{m : ℕ} → {!   !} → Vec A {!   !} → {!   !}
splitAt = {!   !}

splitAt-test1 : {A : Set} → (λ xs → splitAt {A} {10} 0 xs) ≡ (λ xs → [] , xs)
splitAt-test1 = refl

splitAt-test2 : splitAt 2 (1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ [] , [])
splitAt-test2 = refl

splitAt-test3 : splitAt 3 (1 ∷ 2 ∷ 3 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [] , [])
splitAt-test3 = refl

splitAt-test4 : splitAt 3 (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [] , (4 ∷ []))
splitAt-test4 = refl

{-
Definiáld a matrixAdd függvényt, amely a mátrix összeadást valósítja meg.
Segítség: A két mátrixnak milyennek kell lennie, hogy össze lehessen adni azokat?
-}
matrixAdd : {n m : ℕ} → Vec {!   !} {!   !} → Vec {!   !} {!   !} → Vec {!   !} {!   !}
matrixAdd = {!   !}

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

{-
Definiáld a deletions függvény, amely kitöröl a vektorból egy darab
elemet az összes lehetséges módon.
-}
deletions : {A : Set}{n : ℕ} → Vec A {!   !} → Vec {!   !} {!   !}
deletions = {!   !}

deletions-test1 : deletions (1 ∷ 2 ∷ 3 ∷ []) ≡ (2 ∷ 3 ∷ []) ∷ (1 ∷ 3 ∷ []) ∷ (1 ∷ 2 ∷ []) ∷ []
deletions-test1 = refl

deletions-test2 : deletions (false ∷ true ∷ []) ≡ (true ∷ []) ∷ (false ∷ []) ∷ []
deletions-test2 = refl

deletions-test3 : deletions (9 ∷ 8 ∷ 7 ∷ 6 ∷ 5 ∷ []) ≡
  (8 ∷ 7 ∷ 6 ∷ 5 ∷ []) ∷
  (9 ∷ 7 ∷ 6 ∷ 5 ∷ []) ∷
  (9 ∷ 8 ∷ 6 ∷ 5 ∷ []) ∷
  (9 ∷ 8 ∷ 7 ∷ 5 ∷ []) ∷
  (9 ∷ 8 ∷ 7 ∷ 6 ∷ []) ∷ []
deletions-test3 = refl

{-
Definiáld az insertions függvényt, amely egy darab elemet egy vektorba az összes
lehetséges módon beilleszt!
-}
insertions : {A : Set}{n : ℕ} → A → Vec A {!   !} → Vec {!   !} {!   !}
insertions = {!   !}

insertions-test1 : insertions 0 (1 ∷ 2 ∷ 3 ∷ []) ≡
  (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ∷
  (1 ∷ 0 ∷ 2 ∷ 3 ∷ []) ∷
  (1 ∷ 2 ∷ 0 ∷ 3 ∷ []) ∷
  (1 ∷ 2 ∷ 3 ∷ 0 ∷ []) ∷ []
insertions-test1 = refl

insertions-test2 : insertions true (false ∷ []) ≡ (true ∷ false ∷ []) ∷ (false ∷ true ∷ []) ∷ []
insertions-test2 = refl

insertions-test3 : insertions 10 (9 ∷ 11 ∷ 3 ∷ 0 ∷ []) ≡
  (10 ∷ 9 ∷ 11 ∷ 3 ∷ 0 ∷ []) ∷
  (9 ∷ 10 ∷ 11 ∷ 3 ∷ 0 ∷ []) ∷
  (9 ∷ 11 ∷ 10 ∷ 3 ∷ 0 ∷ []) ∷
  (9 ∷ 11 ∷ 3 ∷ 10 ∷ 0 ∷ []) ∷
  (9 ∷ 11 ∷ 3 ∷ 0 ∷ 10 ∷ []) ∷ []
insertions-test3 = refl

-- NEHÉZ FELADAT
{-
Definiáld a permutations függvényt, amely egy vektor összes lehetséges
permutációját megadja!
-}
permutations : {A : Set}{n : ℕ} → Vec A {!   !} → Vec {!   !} {!   !}
permutations = {!   !}

permutations-test1 : permutations (1 ∷ 2 ∷ 3 ∷ []) ≡
  (1 ∷ 2 ∷ 3 ∷ []) ∷
  (2 ∷ 1 ∷ 3 ∷ []) ∷
  (2 ∷ 3 ∷ 1 ∷ []) ∷
  (1 ∷ 3 ∷ 2 ∷ []) ∷
  (3 ∷ 1 ∷ 2 ∷ []) ∷
  (3 ∷ 2 ∷ 1 ∷ []) ∷ []
permutations-test1 = refl

permutations-test2 : permutations (2 ∷ 2 ∷ 9 ∷ 1 ∷ []) ≡
  (2 ∷ 2 ∷ 9 ∷ 1 ∷ []) ∷
  (2 ∷ 2 ∷ 9 ∷ 1 ∷ []) ∷
  (2 ∷ 9 ∷ 2 ∷ 1 ∷ []) ∷
  (2 ∷ 9 ∷ 1 ∷ 2 ∷ []) ∷
  (2 ∷ 9 ∷ 2 ∷ 1 ∷ []) ∷
  (9 ∷ 2 ∷ 2 ∷ 1 ∷ []) ∷
  (9 ∷ 2 ∷ 2 ∷ 1 ∷ []) ∷
  (9 ∷ 2 ∷ 1 ∷ 2 ∷ []) ∷
  (2 ∷ 9 ∷ 1 ∷ 2 ∷ []) ∷
  (9 ∷ 2 ∷ 1 ∷ 2 ∷ []) ∷
  (9 ∷ 1 ∷ 2 ∷ 2 ∷ []) ∷
  (9 ∷ 1 ∷ 2 ∷ 2 ∷ []) ∷
  (2 ∷ 2 ∷ 1 ∷ 9 ∷ []) ∷
  (2 ∷ 2 ∷ 1 ∷ 9 ∷ []) ∷
  (2 ∷ 1 ∷ 2 ∷ 9 ∷ []) ∷
  (2 ∷ 1 ∷ 9 ∷ 2 ∷ []) ∷
  (2 ∷ 1 ∷ 2 ∷ 9 ∷ []) ∷
  (1 ∷ 2 ∷ 2 ∷ 9 ∷ []) ∷
  (1 ∷ 2 ∷ 2 ∷ 9 ∷ []) ∷
  (1 ∷ 2 ∷ 9 ∷ 2 ∷ []) ∷
  (2 ∷ 1 ∷ 9 ∷ 2 ∷ []) ∷
  (1 ∷ 2 ∷ 9 ∷ 2 ∷ []) ∷
  (1 ∷ 9 ∷ 2 ∷ 2 ∷ []) ∷
  (1 ∷ 9 ∷ 2 ∷ 2 ∷ []) ∷ []
permutations-test2 = refl

-- NEHÉZ FELADAT
-- Probléma lesz bárhogyan is, új ötlet kell.
{-
Definiáld a reverse függvényt, amely egy vektor elemeinek a sorrendjét megfordítja.
Megj.: A naív definíció önmagában nem működik. (Sem az akkumulátoros, mindkettőnek ugyanaz lesz a gondja.)

reverse : {A : Set}{n : ℕ} → Vec A n → Vec A n
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ []) -- type error n + 1 ≠ suc n
-}

{-
Bizonyítsd be, hogy a Fin 2 típus izomorf a Bool típussal!
-}
Fin2↔Bool : Fin 2 ↔ Bool
Fin2↔Bool = ?

Fin2-proof1 : ∀ x → fst Fin2↔Bool (snd Fin2↔Bool x) ≡ x
Fin2-proof1 false = refl
Fin2-proof1 true = refl

Fin2-proof2 : ∀ x → snd Fin2↔Bool (fst Fin2↔Bool x) ≡ x
Fin2-proof2 zero = refl
Fin2-proof2 (suc zero) = refl

{-
Definiáld a raiseᵣ, raiseₗ függvényeket, amelyek jobbról, illetve balról
növelik a Fin szintjét.
-}
raiseᵣ : {m : ℕ}(n : ℕ) → Fin m → Fin (n + m)
raiseᵣ = ?

raiseₗ : {m : ℕ} → Fin m → (n : ℕ) → Fin (m + n)
raiseₗ = ?

{-
Bizonyítsd be, hogy a Fin n ⊎ Fin m izomorf Fin (n + m)-mel.

Megj.: Nem tudtam hozzá jó tesztet írni, mert nem triviális
       bizonyítani, hogy oda-vissza és vissza-oda is identitás lesz.
-}
FinIso : {n m : ℕ} → Fin n ⊎ Fin m ↔ Fin (n + m)
FinIso = ?

{-
Definiáld az insertAt függvényt, amely egy elemet egy adott indexű
helyre beszúr. A vektort ne lehessen alulindexelni, illetve egynél többel
túlindexelni se. (Az eggyel való túlindexelés lesz a vektor utolsó utáni eleme,
ha oda szeretnénk az elemet beszúrni.)
-}

insertAt : {A : Set}{n : ℕ} → Vec A n → Fin (suc n) → A → Vec A (suc n)
insertAt = ?

insertAt-test1 : insertAt (1 ∷ 2 ∷ []) zero 0 ≡ 0 ∷ 1 ∷ 2 ∷ []
insertAt-test1 = refl

insertAt-test2 : insertAt (1 ∷ 2 ∷ []) (suc zero) 0 ≡ 1 ∷ 0 ∷ 2 ∷ []
insertAt-test2 = refl

insertAt-test3 : insertAt (1 ∷ 2 ∷ []) (suc (suc zero)) 0 ≡ 1 ∷ 2 ∷ 0 ∷ []
insertAt-test3 = refl

insertAt-test4 : insertAt (false ∷ false ∷ false ∷ []) zero true ≡ true ∷ false ∷ false ∷ false ∷ []
insertAt-test4 = refl

insertAt-test5 : insertAt (false ∷ false ∷ false ∷ []) (suc zero) true ≡ false ∷ true ∷ false ∷ false ∷ []
insertAt-test5 = refl

insertAt-test6 : insertAt (false ∷ false ∷ false ∷ []) (suc (suc zero)) true ≡ false ∷ false ∷ true ∷ false ∷ []
insertAt-test6 = refl

insertAt-test7 : insertAt (false ∷ false ∷ false ∷ []) (suc (suc (suc zero))) true ≡ false ∷ false ∷ false ∷ true ∷ []
insertAt-test7 = refl
{-
Definiáld a removeAt függvényt, amely egy adott indexű helyről eltávolít
egy elemet.
-}

removeAt : {A : Set}{n : ℕ} → Vec A (suc n) → Fin (suc n) → Vec A n
removeAt = ?

removeAt-test1 : removeAt (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) zero ≡ 2 ∷ 3 ∷ 4 ∷ []
removeAt-test1 = refl

removeAt-test2 : removeAt (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) (suc zero) ≡ 1 ∷ 3 ∷ 4 ∷ []
removeAt-test2 = refl

removeAt-test3 : removeAt (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) (suc (suc zero)) ≡ 1 ∷ 2 ∷ 4 ∷ []
removeAt-test3 = refl

removeAt-test4 : removeAt (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) (suc (suc (suc zero))) ≡ 1 ∷ 2 ∷ 3 ∷ []
removeAt-test4 = refl

{-
Definiáld a _[_]%=_ függvényt, amely egy adott indexű helyen
az elemet módosítja úgy, hogy egy adott függvényt meghív
az azon az indexű helyen lévő elemre!
-}

infixl 6 _[_]%=_

_[_]%=_ : {A : Set}{n : ℕ} → Vec A n → Fin n → (A → A) → Vec A n
xs [ i ]%= f = ?

update-test1 : (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) [ zero ]%= (10 *_) ≡ (10 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
update-test1 = refl

update-test2 : (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) [ suc zero ]%= (10 *_) ≡ (1 ∷ 20 ∷ 3 ∷ 4 ∷ 5 ∷ [])
update-test2 = refl

update-test3 : (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) [ suc (suc zero) ]%= (10 +_) ≡ (1 ∷ 2 ∷ 13 ∷ 4 ∷ 5 ∷ [])
update-test3 = refl

update-test4 : (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) [ suc (suc (suc zero)) ]%= (10 +_) ≡ (1 ∷ 2 ∷ 3 ∷ 14 ∷ 5 ∷ [])
update-test4 = refl

update-test5 : (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) [ suc (suc (suc (suc zero))) ]%= (10 +_) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 15 ∷ [])
update-test5 = refl
{-
Definiáld a _[_]≔_ függvényt, amely egy adott indexű helyen lévő
elemet lecserélünk egy másik elemre!
-}

-- \:= = ≔
infixl 6 _[_]≔_

_[_]≔_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A → Vec A n
xs [ i ]≔ y = ?

updateValue-test1 : (1 ∷ 2 ∷ 9 ∷ []) [ zero ]≔ 0 ≡ 0 ∷ 2 ∷ 9 ∷ []
updateValue-test1 = refl

updateValue-test2 : (1 ∷ 2 ∷ 9 ∷ []) [ suc zero ]≔ 0 ≡ 1 ∷ 0 ∷ 9 ∷ []
updateValue-test2 = refl

updateValue-test3 : (1 ∷ 2 ∷ 9 ∷ []) [ suc (suc zero) ]≔ 0 ≡ 1 ∷ 2 ∷ 0 ∷ []
updateValue-test3 = refl

updateValue-test4 : (false ∷ false ∷ []) [ suc zero ]≔ true ≡ false ∷ true ∷ []
updateValue-test4 = refl