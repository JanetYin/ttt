-- open import lib
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Agda.Primitive

-- ez csak libetlenkedés
if_then_else_ : ∀ {i}{A : Set i} → Bool → A → A → A
if true then a else _ = a
if false then _ else a = a

data ⊥ : Set where

-- példa:

_≠0 : ℕ → Set
zero ≠0 = ⊥
(suc _) ≠0 = ⊤_≠0 : ℕ → Set
zero ≠0 = ⊥
(suc _) ≠0 = ⊤

pred : (n : ℕ) {n≠0 : n ≠0} → ℕ
--pred zero {()}
--pred (suc n) {tt} = n
pred (suc n) = n

⊤≡⊤ : ⊤ ≡ ⊤
⊤≡⊤ = refl

ex1 : ℕ
ex1 = pred 4
-- ex2 : ℕ
-- ex2 = pred 0

-- Vec and Fin

infixr 6 _∷_
data Vec {i} (A : Set i) : ℕ → Set i where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

exvec : Vec Bool 3
exvec = (true ∷ (false ∷ true ∷ []))

head : ∀ {i}{A : Set i}{n : ℕ} → Vec A (suc n) → A
head = {!!}

tail : ∀ {i}{A : Set i}{n : ℕ} → Vec A (suc n) → Vec A n
tail (_ ∷ v) = v

-- countDownFrom 3 = 3 ∷ (2 ∷ (1 ∷ []))
countDownFrom : (n : ℕ) → Vec ℕ n
countDownFrom = {!!}

test-countDownFrom : countDownFrom 3 ≡ 3 ∷ 2 ∷ 1 ∷ []
test-countDownFrom = refl

data Fin : ℕ → Set where  -- Fin n = n-elemu halmaz
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

f0 : Fin 0 → ⊥
f0 ()

f1-0 : Fin 1
f1-0 = zero {0}

f2-0 f2-1 : Fin 2
f2-0 = zero {1}
f2-1 = suc {1} f1-0

f3-0 f3-1 f3-2 : Fin 3
f3-0 = zero {2}
f3-1 = suc {2} f2-0
f3-2 = suc {2} f2-1

f4-0 f4-1 f4-2 f4-3 : Fin 4
f4-0 = {!!}
f4-1 = {!!}
f4-2 = {!!}
f4-3 = {!!}

infix 5 _!!_
_!!_ : ∀ {i}{A : Set i}{n : ℕ} → Vec A n → Fin n → A
xs !! zero = {!!}
xs !! suc n = {!!}

test-!! : 3 ∷ 4 ∷ 1 ∷ [] !! (suc (suc zero)) ≡ 1
test-!! = {!!}

-- az n-nek megfelelő Fin (suc n) típusú dolgot
fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero = zero -- egyik a ℕ.zero, másik a Fin.zero
fromℕ (suc n) = suc (fromℕ n)

test-fromℕ : fromℕ 3 ≡ suc (suc (suc zero))
test-fromℕ = refl

-- map f (3 ∷ (4 ∷ [])) = (f 3) ∷ ((f 4) ∷ [])
map : {A B : Set}(f : A → B){n : ℕ} → Vec A n → Vec B n
map f as = {!!}

-- kis kitérő az univerzumokról:
-- C-c C-d Set; mit kapunk?
-- és utána?
-- Russell-paradoxon
-- https://agda.readthedocs.io/en/v2.6.3/language/sort-system.html#sort-system
-- https://agda.readthedocs.io/en/v2.6.3/language/universe-levels.html
id : ∀ {i} {A : Set i} → A → A
id a = a

data List {i} (A : Set i) : Set i where
  []  : List A
  _∷_ : A → List A → List A

lengthList : ∀ {i} {A : Set i} → List A → ℕ
lengthList [] = zero
lengthList (_ ∷ ls) = suc (lengthList ls)

-- ehhez képest:
lengthVec : ∀ {i} {A : Set i} {n : ℕ} → Vec A n → ℕ
lengthVec {n = n} xs = {!!}

-- önállóan
fromList : ∀ {i} {A : Set i}(as : List A) → Vec A (lengthList as)
fromList [] = []
fromList (x ∷ as) = x ∷ (fromList as) --bal oldali ∷ a listáé, jobb oldali a vektoré

-- önállóan
_++_ : ∀ {i} {A : Set i}{m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
_++_ = {!!}

-- önállóan
tabulate : ∀ {i} {A : Set i} {n : ℕ} → (Fin n → A) → Vec A n
tabulate {n = zero} f = []
tabulate {n = suc n} f = f zero ∷ tabulate λ k → f (suc k)

exFin : Fin 3 → ℕ
exFin zero = 98
exFin (suc zero) = 165
exFin (suc (suc zero)) = 223

tabulate-back : ∀ {i} {A : Set i} {n : ℕ} → Vec A n → (Fin n → A)
--tabulate-back xs k = xs !! k
tabulate-back = _!!_

-- NOTE: itt volt óraváltás
----------------------------------------------------------------
-- Sigma types         \GS
-- mint az _×_, de a második tag típusa függ az első tag értékétől
ℕ⁺ : Set
ℕ⁺ = Σ ℕ (λ n → n ≠0)

five⁺ : ℕ⁺
five⁺ = 0 , {!!}

VecWithLen : ∀{i} (A : Set i) → Set i
VecWithLen A = Σ ℕ (Vec A)
--Vec A 0 ⊎ Vec A 1 ⊎ Vec A 2 ⊎ Vec A 3 ⊎...

vwl : VecWithLen ℕ
vwl = 0 , {!!}

-- van a Π is, de annak nem szokott külön neve lenni
-- Vec A 0 × Vec A 1 × Vec A 2 × Vec A 3 ×...
-- de ez nem olyan fontos
Π : ∀ {i j} (A : Set i) (B : A → Set j) → Set (i ⊔ j) -- \Pi
Π A B = (a : A) → B a

pv : Π ℕ (Vec Bool) -- (n : ℕ) → Vec Bool n
pv = {!!}

-- zero⁺ : ℕ⁺
-- zero⁺ = {!!}

filter : ∀ {i}{A : Set i}{n : ℕ}(p : A → Bool) → Vec A n → Σ ℕ (Vec A)
filter p [] = 0 , []
filter p (x ∷ xs) = if (p x) then suc (fst (filter p xs)) , x ∷ (snd (filter p xs))
                                      else (filter p xs)

test-filter : filter (3 <_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ (2 , 4 ∷ 5 ∷ [])
test-filter = refl
