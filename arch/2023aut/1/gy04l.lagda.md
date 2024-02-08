# 4. Gyakorlat

```agda

open import Lib hiding (_+∞_; coiteℕ∞)

open import Lib.Containers.List hiding (zipWith; head; tail)
open import Lib.Containers.Stream hiding (zipWith; coiteStream)

```

## Pozitivítás

Pozitivítás: Létezik-e ez a dolog?

```agda

{-# NO_POSITIVITY_CHECK #-}
data Tm : Set where
  lam : (Tm → Tm) → Tm

app : Tm → (Tm → Tm)
app x (lam f) = f x

self-apply : Tm
self-apply = lam (λ t → app t t)

-- C-c C-n this:
Ω : Tm
Ω = app self-apply self-apply

{-# NO_POSITIVITY_CHECK #-}
data Weird : Set where
  foo : (Weird → ⊥) → Weird

unweird : Weird → ⊥
unweird (foo x) = x (foo x)

bad : ⊥
bad = unweird (foo (λ x → unweird x))

```

## Koinduktivítás

Koninduktivitás: Induktivítás duálisa/párja

Induktivítás: Hogyan tudom egy alap elemből konstruálni a 
többit?

Koninduktivitás: Hogyan tudok egy elemből destruálni 
(szét bontani) újabb elemet?

Stream: végtelen adatfolyam

```plaintext

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream

```
Nézd meg, hogy a konstruktoroknak a következő a típusa 
        head : Stream A → A
        tail : Stream A → Stream A

```agda

zeroes : Stream ℕ
head zeroes = 0
tail zeroes = zeroes

-- by pattern match on n
countDownFrom : ℕ → List ℕ
countDownFrom zero = []
countDownFrom (suc n) = (suc n) ∷ countDownFrom n

-- from n is not by pattern match on n
from : ℕ → Stream ℕ
head (from n) = n
tail (from zero) = from zero
tail (from (suc n)) = from n

-- pointwise addition
zipWith : {A B C : Set} → (A → B → C) → Stream A → Stream B → Stream C
head (zipWith f a b) = f (head a) (head b)
tail (zipWith f a b) = zipWith f (tail a) (tail b)

filterL : {A : Set} → (A → Bool) → List A → List A
filterL {A} f [] = []
filterL {A} f (x ∷ ls) with f x
filterL {A} f (x ∷ ls) | false = filterL f ls
filterL {A} f (x ∷ ls) | true = x ∷ filterL f ls

-- this cannot be defined:
-- filterS : {A : Set} → (A → Bool) → Stream A → Stream A
-- head (filterS P xs) with P (head xs)
-- ... | false = {!   !}
-- ... | true = {!   !}
-- tail (filterS P xs) = {!   !}

-- one element from the first stream, then from the second stream, then from the first, and so on
interleave : {A : Set} → Stream A → Stream A → Stream A
head (interleave a b) = head a
tail (interleave a b) = interleave b a

-- get the n^th element of the stream
get : {A : Set} → ℕ → Stream A → A
get zero s = head s
get (suc n) s = get n (tail s)

-- byIndices [0,2,3,2,...] [1,2,3,4,5,...] = [1,3,4,2,...]
byIndices : {A : Set} → Stream ℕ → Stream A → Stream A
head (byIndices ns s) = get (head ns) s
tail (byIndices ns s) = byIndices (tail ns) s

-- iteℕ : (A : Set) → A → (A → A)  → ℕ → A
--        \______________________/
--         ℕ - algebra

coiteStream : {A : Set} (B : Set) → (B → A) → (B → B) → B → Stream A
--                       \____________________________/
--                        Stream A - coalgebra
head (coiteStream B h t b) = h b
tail (coiteStream B h t b) = coiteStream B h t (t b)

-- ex: redefine the above functions using coiteStream

-- ex: look at conatural numbers in Thorsten's book and do the exercises about them

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
getNumber (calculatorFrom n) = n
add (calculatorFrom n) x = calculatorFrom (n + x)
mul (calculatorFrom n) x = calculatorFrom (n * x)
reset (calculatorFrom n) = calculatorFrom 0

c0 c1 c2 c3 c4 c5 : Machine
c0 = calculatorFrom 0
c1 = add c0 3
c2 = add c1 5
c3 = mul c2 2
c4 = reset c3
c5 = add c4 2

-- conatural numbers
{-
record ℕ∞ : Set where
  coinductive
  field
    pred∞ : Maybe ℕ∞
open ℕ∞
-}

0∞ : ℕ∞
pred∞ 0∞ = nothing
1∞ : ℕ∞
pred∞ 1∞ = just 0∞

∞∞ : ℕ∞
pred∞ ∞∞ = just ∞∞

_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
pred∞ (x +∞ x₁) with pred∞ x
... | nothing = pred∞ x₁
... | just x = just (x +∞ x₁)

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

coiteℕ∞ : {B : Set} → (B → Maybe B) → B → ℕ∞
coiteℕ∞ = {!!}

```

-- TODO, further exercises: network protocols, simple machines: chocolate machine (input: coin, getChocolate, getBackCoins, output: error, chocolate, money back), some Turing machines, animations, IO, repl, shell
  