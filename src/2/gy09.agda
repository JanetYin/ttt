module gy09 where

open import Lib

---------------------------------------------------------
-- equational reasoning
------------------------------------------------------

p4 : (x y : ℕ) → ((x + (y + zero)) + x) ≡ (2 * x + y)
p4 x y =
  x + (y + zero) + x
  ≡⟨ cong (λ a → x + a + x) (comm+ y 0) ⟩
  x + (zero + y) + x
  ≡⟨ comm+ (x + (zero + y)) x ⟩
  x + (x + (zero + y))
  ≡⟨ cong (λ a → x + a) (sym (assoc+ x 0 y)) ⟩
  x + ((x + zero) + y)
  ≡⟨ sym (assoc+ x (x + zero) y) ⟩
  x + (x + zero) + y ∎

p3 : (a b : ℕ) → a + a + b + a * 0 ≡ 2 * a + b
p3 a b =
     cong (λ x → a + a + b + x) (nullr* a)
  ◾ idr+ (a + a + b)
  ◾ cong (λ x → a + x + b) (sym (idr+ a))

p2 : (a b c : ℕ) → c * (b + 1 + a) ≡ a * c + b * c + c
p2 = {!!}

-- \==n = ≢
p9' : 0 ≢ the ℕ 1
p9' ()
-- Axióma 1: Konstruktorok diszjunktak, tehát különböző nevű konstruktorok tényleg különbözőek

p9 : 2 * 2 ≢ 5 * 1
p9 ()
-- Axióma 2: Konstruktorok injektívek, tehát egyenlőség két oldalán lévő azonos konstruktorokat le lehet nyelni.

suc-inj : ∀{x y} → suc x ≡ suc y → x ≡ y
suc-inj refl = refl

-- Egyszerűbb, amikor mondani kell egy ellenpéldát:
p10 : ¬ ((n : ℕ) → n + 2 ≡ n + 1)
p10 f with f 0
... | ()

-- ...mintsem bizonyítani, hogy ez a kettő sosem lesz egyenlő:
p11 : (n : ℕ) → n + 2 ≢ n + 1
p11 (suc n) e = p11 n (suc-inj e)
-- A függvény nem végtelen; nem felejtjük el, hogy a 0 is le van kezelve, csak agda magától tudja, hogy baromság.

-- Mókásabb helyzet.
p11'' : ¬ Σ ℕ (λ n → n + 3 ≡ n + 1)
p11'' = f g where
  g : (n : ℕ) → n + 3 ≢ n + 1
  g (suc n) e = g n (suc-inj e)
  f : ((n : ℕ) → n + 3 ≢ n + 1) → ¬ Σ ℕ (λ n → n + 3 ≡ n + 1)
  f h (n , e) = h n e

p12 : ¬ Σ ℕ (λ n → n + n ≡ 3)
p12 = {!   !}

[m+n]^2=m^2+2mn+n^2 : (m n : ℕ) → (m + n) * (m + n) ≡ m * m + 2 * m * n + n * n
[m+n]^2=m^2+2mn+n^2 = {!!}

{-
infixr 8 _^_
_^_ : ℕ → ℕ → ℕ
x ^ zero  = 1
x ^ suc n = x * x ^ n
-}

p1 : (a b : ℕ) → (a + b) ^ 2 ≡ a ^ 2 + 2 * a * b + b ^ 2
p1 = {!!}

0^ : (n : ℕ) → 0 ^ (suc n) ≡ 0
0^ = {!!}

^0 : (a : ℕ) → a ^ 0 ≡ 1
^0 = {!!}

1^ : (n : ℕ) → 1 ^ n ≡ 1
1^ = {!!}

^1 : (a : ℕ) → a ^ 1 ≡ a
^1 = {!!}

^+ : (a m n : ℕ) → a ^ (m + n) ≡ a ^ m * a ^ n
^+ = {!!}

^* : (a m n : ℕ) → a ^ (m * n) ≡ (a ^ m) ^ n
^* = {!!}

*^ : (a b n : ℕ) → (a * b) ^ n ≡ a ^ n * b ^ n
*^ = {!!}
