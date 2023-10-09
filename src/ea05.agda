open import Lib hiding (T; _-_)

iteℕ : {A : Set} → A → (A → A) → ℕ → A
iteℕ z s zero = z
iteℕ z s (suc n) = s (iteℕ z s n)

_+'_ : ℕ → ℕ → ℕ
m +' n = iteℕ n suc m
{-
⊤η    :   t = tt
×η    :   t = (fst t , snd t)
Boolβ :   if true then u else v = u

(λ x → iteℕ zero (λ z → zero) (suc zero)) =
(λ x → (λ z → zero) (iteℕ zero (λ z → zero) zero)) =
(λ x → zero)

(λ x → 1 + 1) = (λ x → 2)
(λ x → x + 1) 1 = 1 + 1 = 2 = (λ x → 2) 12334
(λ x → 2) ≠ (λ x → 3)

(λ x → if x then x else x) ≠ (λ x → x)
(λ x → iteℕ 0 suc x) = (λ x → x + 0) ≠ (λ x → x) = (λ x → zero + x) = (λ x → 0 + x)
-}

-- adattípusok / induktív típusok (pozitivitás)

data T : Set where
  leaf  : T
  node2 : T → T → T
  node3 : T → T → T → T
  node2' : (Bool → T) → T

-- T = { leaf , node leaf leaf , node leaf (node leaf leaf) }
{-
  /\      /|\
 /\        /\      node3 leaf (node2 leaf (node3 leaf leaf leaf)) leaf
  /\        /|\
-}
t : T
t = node2 (node2 leaf (node2 leaf leaf)) leaf

data T' : Set where
  leaf : T'
  node : (ℕ → T') → T'

-- magassaga 2
t' : T'
t' = node (λ _ → node (λ _ → leaf))

-- HF: megadni olyan t'' : T' -t, melyre nincs eleg mely godor, hogy beleferjen

data Ures : Set where
  con : Ures → Ures

ures2ures : Ures → ⊥                -- dead code
ures2ures (con t₁) = ures2ures t₁

{-# NO_POSITIVITY_CHECK #-}
data T'' : Set where
  node : (T'' → ⊥) → T''

f : T'' → ⊥
f (node x) = x (node x)

bot : ⊥
bot = f (node f)

-- koinduktív típusok

-- induktiv ⊥,⊎           koinduktiv ⊤,×
-- konstruktorokkal       destruktorokkal      (megadas)
-- pattern matching-gel   copattern matching-gel
--   bontjuk le             epitjuk fel

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream public

zeroes : Stream ℕ
head zeroes = 0
tail zeroes = zeroes

-- countFrom 0 = [0,1,2,3,4,5,6,...]
-- countFrom n = [n,1+n,2+n,3+n,...]
countFrom : ℕ → Stream ℕ
head (countFrom n) = n
tail (countFrom n) = countFrom (1 + n)

-- osszefuz : {A : Set} → Stream A → Stream A → Stream A

open import Lib.Containers.List hiding (filter; head; tail)

filter : {A : Set} → (A → Bool) → List A → List A
filter f [] = []
filter f (x ∷ xs) = if f x then
   x ∷ (filter f xs)
 else
   filter f xs

-- ez csak akkor adhato meg, ha valahogy tudom, hogy xs-re vegtelen sok esetben ad true-t az f
{-
filterStream : {A : Set} → (A → Bool) → Stream A → Stream A
head (filterStream f xs) = 
  if f (head xs) then
      head xs
    else
      head (filterStream f (tail xs))
tail (filterStream f xs) = {!!}
-}

-- iteList : {A C : Set} → C → (A → C → C) → List A → C
coitStream : {A C : Set} → (C → A) → (C → C) → C → Stream A
head (coitStream hd tl seed) = hd seed
tail (coitStream hd tl seed) = coitStream hd tl (tl seed)

countFrom0 = coitStream {ℕ}{ℕ} (λ x → x) suc 0

_>_ : ℕ → ℕ → Bool
zero > _ = false
suc m > zero = true
suc m > suc n = m > n

_-_ : ℕ → ℕ → ℕ
zero - _ = zero
suc m - zero = suc m
suc m - suc n = m - n

-- elso parameter = fuel, uzemanyag
gcd' : ℕ → ℕ → ℕ → ℕ
gcd' 0 n m = 42
gcd' (suc i) n m = if n > m then gcd' i (n - m) m else
  if m > n then gcd' i n (m - n) else n

gcd : ℕ → ℕ → ℕ
gcd n m = gcd' (n + m) n m

-- gcd (suc n) m = ....  gcd n m ...

-- jovo ora 2 perccel rovidebb, FÜGGŐ TÍPUS!

