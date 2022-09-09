module me3 where

open import me1sol
open import me2sol

-- data ℕ : Set where
--   zero : ℕ
--   suc  : ℕ → ℕ
-- {-# BUILTIN NATURAL N #-}

pred' : ℕ → ℕ
pred' zero    = zero
pred' (suc n) = n

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

-- FEL: ugy add meg, hogy proj₁ MaybeEq (proj₂ MaybeEq x) = x teljesüljön minden x : P ⊎ ⊤-ra!
MaybeEq : Maybe P ⇔ P ⊎ ⊤
MaybeEq = {!!}

pred : ℕ → Maybe ℕ
pred zero    = nothing
pred (suc n) = just n

zerosuc : Maybe ℕ → ℕ
zerosuc nothing = zero
zerosuc (just n) = suc n

-- FEL: mutasd meg egyenlosegi ervelessel, hogy pred (zerosuc x) = x es zerosuc (pred y) = y minden x-re es y-ra!

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

-- FEL: mutasd meg egyenlosegi ervelessel, hogy double 3 = 6!

-- FEL: add meg triple-t _+_ hasznalata nelkul, rekurzivan!

-- _+_ : ℕ → ℕ → ℕ
-- zero + n = n
-- suc m + n = suc (m + n)

-- FEL: szorzas
_*_ : ℕ → ℕ → ℕ
m * n = {!!}

-- FEL: hatvanyozas
_^_ : ℕ → ℕ → ℕ
m ^ n = {!!}

-- FEL: felezes
half : ℕ → ℕ
half = {!!}

-- Ackermann

ack : ℕ → ℕ → ℕ → ℕ
-- ack 0 m n = suc n
-- ack 1 m n = m + n = m times (ack 0 m) on n = m times suc on n
-- ack 2 m n = m * n = m times (ack 1 m) on n = m times (m+) on n
-- ack 3 m n = m ^ n
-- ...

ack zero                      m n       = suc n
ack (suc zero)                m zero    = m
ack (suc (suc zero))          m zero    = 0
ack (suc (suc (suc zero)))    m zero    = 1
ack (suc (suc (suc (suc l)))) m zero    = m
ack (suc l)                   m (suc n) = ack l m (ack (suc l) m n)

-- iterator

-- double using iterator

