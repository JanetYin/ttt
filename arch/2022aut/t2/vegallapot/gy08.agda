open import lib
open import Agda.Builtin.Nat as ℕ

-- Vec and Fin

-- Vec: a container which "knows" its length
infixr 6 _∷_        --\::
data Vec (A : Set) : ℕ → Set where           --# TODO: check out the syntax
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

firstvec : Vec Bool 4
firstvec = true ∷ false ∷ true ∷ true ∷ []

head : {A : Set}{n : ℕ} → Vec A (suc n) → A              --you could not write this for a list!
head (x ∷ _) = x

tail : {A : Set}{n : ℕ} → Vec A (suc n) → Vec A n        --this you could, but it wouldn't be perfect
tail (_ ∷ xs) = xs

countDownFrom : (n : ℕ) → Vec ℕ n
countDownFrom zero = []
countDownFrom (suc n) = (suc n) ∷ countDownFrom n

test-countDownFrom : countDownFrom 3 ≡ 3 ∷ 2 ∷ 1 ∷ []
test-countDownFrom = refl

data Fin : ℕ → Set where  -- Fin n: finite set with n elements ({0, 1, ..., n})
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

{-
f0 : Fin 0 → ⊥
f0 ()

f1-0 : Fin 1
f1-0 = zero {0}

f2-0 f2-1 : Fin 2
f2-0 = zero {1}
f2-1 = suc (zero {0})

f3-0 f3-1 f3-2 : Fin 3
f3-0 = zero {2}
f3-1 = suc (zero {1})
f3-2 = suc (suc (zero {0}))

f4-0 f4-1 f4-2 f4-3 : Fin 4
f4-0 = zero {3}
f4-1 = suc (zero {2})
f4-2 = suc (suc (zero {1}))
f4-3 = suc (suc (suc (zero {0})))
-}

{-
zero {0}
zero {1}  | suc (zero {0})
zero {2}  | suc (zero {1}) | suc (suc (zero {0}))
zero {3}  | suc (zero {2}) | suc (suc (zero {1})) | suc (suc (suc (zero {0})))
-}

f0 : Fin 0 → ⊥
f0 ()

f1-0 : Fin 1
f1-0 = zero

f2-0 f2-1 : Fin 2
f2-0 = zero
f2-1 = suc (zero)

f3-0 f3-1 f3-2 : Fin 3
f3-0 = zero
f3-1 = suc (zero)
f3-2 = suc (suc (zero))

f4-0 f4-1 f4-2 f4-3 : Fin 4
f4-0 = zero
f4-1 = suc (zero)
f4-2 = suc (suc (zero))
f4-3 = suc (suc (suc (zero)))

--from the standard library
fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero = zero {zero}
fromℕ (suc n) = suc (fromℕ n)

{-
--from the standard library, too
fromℕ< : {m n : ℕ} →  m ℕ.< n → Fin n
fromℕ< {zero}  {suc n} z<s = zero
fromℕ< {suc m} {suc n} (s<s m<n) = suc (fromℕ< m<n)
-}

infix 5 _!!_
_!!_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A         --guarantees that the index is within bounds
x ∷  _ !!  zero = x
x ∷ xs !! suc n = xs !! n

test-!! : 3 ∷ 4 ∷ 1 ∷ [] !! (suc zero) ≡ 4
test-!! = refl

{-
test-fromℕ : fromℕ 3 ≡ suc (suc (suc zero))             --also a dependent type!
test-fromℕ = refl
-}

--# homework
map : {A B : Set}(f : A → B){n : ℕ} → Vec A n → Vec B n
map f as = {!!}

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

length : {A : Set} → List A → ℕ
length [] = zero
length (_ ∷ xs) = suc (length xs)

fromList : {A : Set} (as : List A) → Vec A (length as)
fromList []       = []
fromList (x ∷ xs) = x ∷ fromList xs

--# homework
_++_ : {A : Set}{m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
_++_ = {!!}

{-
there are no infinite lists:
zeroes : List ℕ
zeroes = 0 ∷ zeroes
-}

toℕ : {n : ℕ} → Fin n → ℕ
toℕ zero = zero
toℕ (suc k) = suc (toℕ k)

--                             finite series
tabulate : {n : ℕ}{A : Set} → (Fin n → A) → Vec A n
tabulate {zero} {_} a = []
tabulate {suc n} {_} a = a zero ∷ tabulate (λ k → a (suc k))

onetofive : Vec ℕ 5
onetofive = tabulate (λ k → suc (suc (toℕ k)))

-- Sigma types  (Σ is \GS)

open import Agda.Builtin.Sigma

{-
infixr 4 _,_
record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

{-# BUILTIN SIGMA Σ #-}    --again, dark magic


why Σ?
Σ ℕ B is like (B 0) ⊎ (B 1) ⊎ (B 2) ⊎ (B 3) ⊎...
-}

sig : Σ ℕ (Vec Bool)
sig = 4 , true ∷ true ∷ true ∷ false ∷ []

ss : Σ Bool (λ {true → ℕ; false → Bool}) --like ℕ ⊎ Bool
ss = true , 5

filter : {A : Set}{n : ℕ}(f : A → Bool) → Vec A n → Σ ℕ (Vec A)      --it can be of any length, but we want to have the exact length within the type
filter p [] = 0 , []
filter {A = A} p (x ∷ xs) = if p x then suc (fst last) , x ∷ (snd last) else last
  where
  last : Σ ℕ (Vec A)
  last = filter p xs

test-filter : filter (3 <_) (4 ∷ 3 ∷ 2 ∷ 5 ∷ []) ≡ (2 , 4 ∷ 5 ∷ [])
test-filter = refl

--isomorphisms
--a bit like summation
Σ=⊎ : {A B : Set} → Σ Bool (if_then A else B) ↔ A ⊎ B
Σ=⊎ = (λ {(true , a) → inl a ;
          (false , b) → inr b})
        ,
       λ {(inl a) → true , a ;
           (inr b) → false , b}
{-
Σ=⊎ = part₁ , part₂
  where
  part₁ : ...
  part₁ (true , a) = ?
  part₁ (false , b) = ?
  ...
-}

Σ=× : {A B : Set} → Σ A (λ _ → B) ↔ A × B
Σ=× = (λ (a , b) → (a , b)) ,
       λ (a , b) → (a , b)

Π=→ : {A B : Set} → ((a : A) → (λ _ → B) a) ≡ (A → B)
Π=→ = refl

--# homework
→=× : {A B : Set} → ((b : Bool) → if b then A else B) ↔ A × B
→=× = (λ f → f true , f false) ,
       λ {(a , _) true  → a ;
          (_ , b) false → b}

--# should we do this here?
dependentCurry : {A : Set}{B : A → Set}{C : (a : A) → B a → Set} →
  ((a : A)(b : B a) → C a b) ↔ ((w : Σ A B) → C (fst w) (snd w))         --first is curriable, second essentially gets a tuple
dependentCurry = {!!} , {!!}

∀×-distr  : {A : Set}{P : A → Set}{Q : A → Set} → ((a : A) → P a × Q a)  ↔ ((a : A) → P a) × ((a : A) → Q a)
∀×-distr = {!!}

--#homework
Bool=Fin2 : Bool ↔ Fin 2
Bool=Fin2 = {!!} , {!!}


Fin1+3=Fin4 : Fin (1 + 3) ↔ Fin 1 ⊎ Fin 3
Fin1+3=Fin4 = {!!}

-- relating Fin m ⊎ Fin n and Fin (m + n)

-- to the left
inj₁f : {m n : ℕ} → Fin m → Fin (m + n)
inj₁f {suc m} {n} (zero {m}) = zero {m + n}
inj₁f {suc m} {n} (suc {m} i) = suc {m + n} (inj₁f i)

{-
Fin 5  |    .  .  .  .  .
            |  |  |  |  |
Fin 8  |    .  .  .  .  .  .  .  .
-}

test-inj₁f : inj₁f {3}{4} (suc (suc zero)) ≡ suc (suc (zero))
test-inj₁f = refl

--to the right
inj₂f : {m n : ℕ} → Fin n → Fin (m + n)
inj₂f {m = zero} i = i
inj₂f {m = suc m} i = suc (inj₂f {m = m} i)

{-
Fin 5  |    .  .  .  .  .
                      \  \
                       \  \
                        \  \
                         \  \
                          \  \
                              \
                               \
                                \
Fin 8  |    .  .  .  .  .  .  .  .
-}

test-inj₂f : inj₂f {3}{4} (suc (suc zero)) ≡ suc (suc (suc (suc (suc zero))))
test-inj₂f = refl

f : {m n : ℕ} → Fin m ⊎ Fin n → Fin (m + n)
f (inl i) = inj₁f i
f (inr i) = inj₂f i

casef : {m n : ℕ}{C : Set} → (Fin m → C) → (Fin n → C) → Fin (m + n) → C   --concatenate two finite series
casef {m = zero} f g i = g i
casef {m = suc m} f g zero = f zero
casef {m = suc m} f g (suc i) = casef {m} (λ k → f (suc k)) g i

test-casef : casef {3}{3} (λ i → i) (λ i → i) (suc (suc zero)) ≡ suc (suc zero)
test-casef = refl
test-casef' : casef {3}{3} (λ i → i) (λ i → i) (suc (suc (suc zero))) ≡ zero
test-casef' = refl
test-casef'' : casef {3}{3} (λ i → i) (λ i → i) (suc (suc (suc (suc zero)))) ≡ suc zero
test-casef'' = refl

--#NOTE: learn until here

-- use inj₁f,inj₂f in one direction and "casef inj₁ inj₂" in the other direction
Fin+ : {m n : ℕ} → Fin (m + n) ↔ Fin m ⊎ Fin n
Fin+ = {!!}

--# skip these?
-- this might be hard
Fin* : {m n : ℕ} → Fin (m * n) ↔ Fin m × Fin n
Fin* = {!!}

-- n-1
--  Σ  a i = a 0 + a 1 + ... + a (n-1)
-- i=0

Σℕ : (n : ℕ) → (Fin n → ℕ) → ℕ   --sum of an n-length finite series
Σℕ zero    a = 0
Σℕ (suc n) a = a zero + Σℕ n (λ i → a (suc i))

-- not very easy
Σ+ : (n : ℕ)(a : Fin n → ℕ) → Σ (Fin n) (λ i → Fin (a i)) ↔ Fin (Σℕ n a)
Σ+ = {!!}

-- n-1
--  Π  a i = a 0 * a 1 * ... * a (n-1)
-- i=0

Πℕ : (n : ℕ) → (Fin n → ℕ) → ℕ
Πℕ zero    a = 0
Πℕ (suc n) a = a zero * Πℕ n (λ i → a (suc i))

-- not very easy
Π* : (n : ℕ)(a : Fin n → ℕ) → ((i : Fin n) → Fin (a i)) ↔ Fin (Πℕ n a)
Π* = {!!}
