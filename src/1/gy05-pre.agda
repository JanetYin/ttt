module gy05 where

open import Lib hiding (fromℕ ; minMax; _+∞_; coiteℕ∞; ∞)
open import Lib.Containers.Vector hiding (head; tail; map; length; _++_)
open import Lib.Containers.List hiding (head; tail; map; _++_; filter)

-- simple calculator (internally a number, you can ask for the number, add to that number, multiply that number, make it zero (reset))
record Machine : Set where
  coinductive
  field
    getNumber : ℕ
    add       : ℕ → Machine
    mul       : ℕ → Machine
    reset     : Machine
open Machine

calculatorFrom : ℕ → Machine
calculatorFrom n = {!!}

c0 c1 c2 c3 c4 c5 : Machine
c0 = calculatorFrom 0
c1 = add c0 3
c2 = add c1 5
c3 = mul c2 2
c4 = reset c3
c5 = add c4 2

-- FELADAT: Készítsünk egy csokiautomatát.
-- A gépbe tudunk pénzt dobálni (ez legyen ℕ, ennyit adjunk hozzá a jelenlegi kreditünhöz).
-- A tranzakciót meg tudjuk szakítani, a kredit 0 lesz és visszaadja a pénzünket.
-- Legyen 3 termékünk, ezek egyenként kerülnek valamennyibe és van belőlük a gépben valamennyi.
-- + Twix: 350-be kerül, kezdetben van a gépben 50 darab.
-- + Croissant: 400-ba kerül, kezdetben van 75 darab.
-- + Snickers: 375-be kerül, kezdetben van 60 darab.
-- Tudunk 1 terméket vásárolni, ha van elég bedobott pénzünk, ekkor a darabszámból vonjunk le egyet (ha lehet) és adjuk vissza a visszajárót, a kreditet nullázzuk le.
-- A gép tartalmát újra tudjuk tölteni, ekkor twix-ből legyen újra 50 darab, croissant-ból 75, snickers-ből pedig 60.



-----------------------------------------------------
-- conatural numbers
-----------------------------------------------------
{-
record ℕ∞ : Set where
  coinductive
  field
    pred∞ : Maybe ℕ∞
open ℕ∞
-}

0∞ : ℕ∞
0∞ = ?

1∞ : ℕ∞
1∞ = ?

2∞ : ℕ∞
2∞ = ?

_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
_+∞_ = {!!}

-- Ez a függvény létezik, ezzel lehet megnézni
-- egy conat tényleges értékét.
-- Az első paraméter a fuel, maximum ezt a természetes számot tudja visszaadni.
-- Második paraméter a conat, amire kíváncsiak vagyunk.
-- Értelemszerűen ∞-re mindig nothing az eredmény.
{-
ℕ∞→ℕ : ℕ → ℕ∞ → Maybe ℕ
ℕ∞→ℕ zero _ = nothing
ℕ∞→ℕ (suc n) c with pred∞ c
... | zero∞ = just 0
... | suc∞ b with ℕ∞→ℕ n b
... | nothing = nothing
... | just x = just (suc x)
-}

coiteℕ∞ : {B : Set} → ?
coiteℕ∞ = {!!}

-- Vec and Fin
{-
infixr 5 _∷_
data Vec (A : Set)
-}
head : {A : Set}{n : ℕ} → {!   !}
head = {!!}

tail : {A : Set}{n : ℕ} → {!   !}
tail = {!!}

countDownFrom : (n : ℕ) → Vec ℕ n
countDownFrom = {!!}

test-countDownFrom : countDownFrom 3 ≡ 3 ∷ 2 ∷ 1 ∷ []
test-countDownFrom = refl

_++_ : {A : Set}{m n : ℕ} → {!   !} → {!   !} → {!   !}
xs ++ ys = {!!}

map : {!   !}
map f xs = {!!}

-- Melyik az a függvény, amit nem tudunk totálisan megírni (még)?
-- Indexelés! Kell hozzá új ötlet!

{-
data Fin : ℕ → Set where  -- Fin n = n-elemu halmaz
  fzero : ?
  fsuc  : ?
-}

f0 : Fin 0 → ⊥
f0 x = {!!}

f1-0 : Fin 1
f1-0 = {!!}

f2-0 f2-1 : Fin 2
f2-0 = {!!}
f2-1 = {!!}

f3-0 f3-1 f3-2 : Fin 3
f3-0 = {!!}
f3-1 = {!!}
f3-2 = {!!}

f4-0 f4-1 f4-2 f4-3 : Fin 4
f4-0 = {!!}
f4-1 = {!!}
f4-2 = {!!}
f4-3 = {!!}

-- Lib-ben a unicode ‼ az indexelés.
infixl 9 _!!_
_!!_ : {A : Set}{n : ℕ} → {!   !}
xs !! n = {!!}

test-!! : (the ℕ 3 ∷ 4 ∷ 1 ∷ []) !! (fsuc (fsuc fzero)) ≡ 1
test-!! = refl

test2-!! : (the ℕ 3 ∷ 4 ∷ 1 ∷ 0 ∷ 10 ∷ []) !! 3 ≡ 0 -- 3-as literál a !! után valójában Fin 5 típusú.
test2-!! = refl

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ = {!!}

test-fromℕ : fromℕ 3 ≡ fsuc (fsuc (fsuc fzero))
test-fromℕ = refl

{-
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A
-}

{-
length : {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)
-}

fromList : {A : Set}(as : List A) → {!    !}
fromList = {!!}

tabulate : {n : ℕ}{A : Set} → (Fin n → A) → Vec A n
tabulate = {!!}

test-tabulate : tabulate (the (Fin 3 -> ℕ) (λ {fzero -> 6; (fsuc fzero) -> 9; (fsuc (fsuc fzero)) -> 2}))
                  ≡ 6 ∷ 9 ∷ 2 ∷ []
test-tabulate = refl

-- Sigma types

what : Σ ℕ (Vec Bool)
what = {!   !} , {!   !}

filter : {A : Set}{n : ℕ}(f : A → Bool) → Vec A n → Σ ℕ (Vec A) -- ezen lehet pontosítani, hiszen n elemnél nem kéne legyen benne több elem soha.
filter = {!   !}

test-filter : filter {ℕ} (3 <ᵇ_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ (2 , 4 ∷ 5 ∷ [])
test-filter = refl

smarterLengthList : ∀{i}{A : Set i}{n : ℕ} → List A → {!    !}
smarterLengthList = {!   !}

smarterLengthVec : ∀{i}{A : Set i}{n : ℕ} → Vec A n → {!    !}
smarterLengthVec = {!   !}

minMax' : ℕ → ℕ → ℕ × ℕ
minMax' n m = {!   !}

-- Ugyanez sokkal jobban, de leginkább pontosabban.
-- Az előző változatban vissza tudok adni csúnya dolgokat is.
-- Pl. konstans (0 , 0)-t.
minMax : (n m : ℕ) → Σ (ℕ × ℕ) (λ (a , b) → a ≤ℕ b × (n ≤ℕ m × n ≡ a × m ≡ b ⊎ m ≤ℕ n × n ≡ b × m ≡ a))
minMax n m = {!   !}
