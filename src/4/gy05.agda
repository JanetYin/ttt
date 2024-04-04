module gy05 where

open import Lib hiding (fromℕ ; minMax)
open import Lib.Containers.Vector hiding (head; tail; map; length; _++_)
open import Lib.Containers.List hiding (head; tail; map; _++_; filter)











-- \ge
_≥_ : ℕ → ℕ → Bool
zero ≥ zero = true
zero ≥ suc k = false
suc n ≥ zero = true
suc n ≥ suc k = n ≥ k

BoolToSet : Bool → Set
BoolToSet false = ⊥
BoolToSet true = ⊤

subtraction : (n : ℕ) → (k : ℕ) → BoolToSet (n ≥ k) → ℕ
subtraction zero zero x = zero
subtraction (suc n) zero x = suc n
subtraction (suc n) (suc k) x = subtraction n k x

bothNotZero : ℕ → ℕ → Bool
bothNotZero zero zero = false
bothNotZero zero (suc k) = true
bothNotZero (suc n) k = true

power : (n : ℕ) → (k : ℕ) → BoolToSet (bothNotZero n k) → ℕ
power zero (suc k) x = zero
power (suc n) zero x = 1
power (suc n) (suc k) x = (suc n) * (power (suc n) k tt)

-- open import Agda.Builtin.Nat renaming (Nat to ℕ)
-- open import Agda.Builtin.Bool
-- open import Agda.Builtin.Unit
-- data ⊥ : Set where










-- Vec and Fin
{-
infixr 5 _∷_
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)
-}
head : {A : Set}{n : ℕ} → Vec A (suc n) → A  
head (x ∷ v) = x

tail : {A : Set}{n : ℕ} →  Vec A (suc n) → Vec A n
tail (x ∷ v) = v

countDownFrom : (n : ℕ) → Vec ℕ n
countDownFrom = {!!}

test-countDownFrom : countDownFrom 3 ≡ 3 ∷ 2 ∷ 1 ∷ []
test-countDownFrom = refl

_++_ : {A : Set}{m n : ℕ} →  Vec A m   → Vec A n  →  Vec A (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = {!!}

map : {A B : Set} →   {n : ℕ} → (A → B) → Vec A n → Vec B n
map f xs = {!!}

zip : {!!} -- zip two lists
zip = {!!}

takeV : {!!}
takeV = {!!}



combinations : {A B : Set}{n k : ℕ} → Vec A n → Vec B k → Vec (A × B) ( n * k)
combinations [] ys = []
combinations (x ∷ xs) ys = map (λ y → x , y) ys ++ (combinations xs ys)


-- Melyik az a függvény, amit nem tudunk totálisan megírni (még)?
-- Indexelés! Kell hozzá új ötlet!

{-
data Fin : ℕ → Set where  -- Fin n = n-elemu halmaz
  fzero : {n : ℕ} → Fin (suc n)
  fsuc  : {n : ℕ} → Fin n → Fin (suc n)
-}

f0 : Fin 0 → ⊥
f0 ()

f1-0 : Fin 1
f1-0 = fzero

f2-0 f2-1 : Fin 2
f2-0 = fzero
f2-1 = fsuc f1-0

f3-0 f3-1 f3-2 : Fin 3
f3-0 = fzero
f3-1 = fsuc f2-0
f3-2 = fsuc f2-1

f4-0 f4-1 f4-2 f4-3 : Fin 4
f4-0 = fzero
f4-1 = fsuc f3-0
f4-2 = fsuc f3-1
f4-3 = fsuc f3-2

-- Lib-ben a unicode ‼ az indexelés.
infixl 9 _!!_
_!!_ : {A : Set}{n : ℕ} →   Vec A n  → Fin n → A
(x ∷ xs) !! fzero = x
(x ∷ xs) !! fsuc n = xs !! n

test-!! : (the ℕ 3 ∷ 4 ∷ 1 ∷ []) !! (fsuc (fsuc fzero)) ≡ 1
test-!! = refl

test2-!! : (the ℕ 3 ∷ 4 ∷ 1 ∷ 0 ∷ 10 ∷ []) !! 3 ≡ 0 -- 3-as literál a !! után valójában Fin 5 típusú.
test2-!! = refl

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ = {!!}

{-
data Σ (A : Set)(B : A → Set) : Set where
  _,_ : (a : A) → B a → A × B
-}

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

toList : {A : Set}{n : ℕ}(as : Vec A n) → List A
toList [] = []
toList (x ∷ as) = x ∷ toList as

fromList : {A : Set}(as : List A) →    Vec A (length as) 
fromList = {!!}

-- \GS \Sigma
fromList' : {A : Set} → List A → Σ ℕ λ n → Vec A n
fromList' [] = 0 , []
fromList' (x ∷ vs) = (suc (fst (fromList' vs))) , x ∷ snd (fromList' vs)

tabulate : {n : ℕ}{A : Set} → (Fin n → A) → Vec A n
tabulate = {!!}

test-tabulate : tabulate (the (Fin 3 -> ℕ) (λ {fzero -> 6; (fsuc fzero) -> 9; (fsuc (fsuc fzero)) -> 2}))
                  ≡ 6 ∷ 9 ∷ 2 ∷ []
test-tabulate = refl

-- Sigma types

what : Σ ℕ (Vec Bool)
what = {!   !} , {!   !}

take' : {A : Set}{n : ℕ} → ℕ → Vec A n → Σ ℕ λ n → Vec A n
take' = {!!}

drop' : {A : Set}{n : ℕ} → ℕ → Vec A n → Σ ℕ λ n → Vec A n
drop' = {!!}

filter : {A : Set}{n : ℕ}(f : A → Bool) → Vec A n → Σ ℕ (Vec A) -- ezen lehet pontosítani, hiszen n elemnél nem kéne legyen benne több elem soha.
filter f [] = {!!}
filter f (x ∷ x₁) with f x
... | false = {!!}
... | true = {!!}

test-filter : filter {ℕ} (3 <ᵇ_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ (2 , 4 ∷ 5 ∷ [])
test-filter = refl

smarterLengthList : ∀{i}{A : Set i}{n : ℕ} → List A → {!    !}
smarterLengthList = {!   !}

smarterLengthVec : ∀{i}{A : Set i}{n : ℕ} → Vec A n → {!    !}
smarterLengthVec = {!   !}



----------------------------------


minMax' : ℕ → ℕ → ℕ × ℕ
minMax' n m = {!   !}

-- Ugyanez sokkal jobban, de leginkább pontosabban.
-- Az előző változatban vissza tudok adni csúnya dolgokat is.
-- Pl. konstans (0 , 0)-t.
minMax : (n m : ℕ) → Σ (ℕ × ℕ) (λ (a , b) → a ≤ℕ b × (n ≤ℕ m × n ≡ a × m ≡ b ⊎ m ≤ℕ n × n ≡ b × m ≡ a))
minMax n m = {!   !}
