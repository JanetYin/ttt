module gy10 where

open import Lib

---------------------------------------------------------
-- equational reasoning
------------------------------------------------------

p4 : (x y : ℕ) → ((x + (y + zero)) + x) ≡ (2 * x + y)
p4 x y =
     comm+ (x + (y + 0)) x
  ◾ cong (λ a → x + (x + a)) (comm+ y 0)
  ◾ cong (x +_) (sym (assoc+ x 0 y))
  ◾ sym (assoc+ x (x + 0) y)

p3 : (a b : ℕ) → a + a + b + a * 0 ≡ 2 * a + b
p3 a b =
  a + a + b + a * 0
  ≡⟨ cong (λ x → a + a + b + x) (comm* a 0) ⟩
  a + a + b + 0
  ≡⟨ idr+ (a + a + b) ⟩
  a + a + b
  ≡⟨ cong (λ x → a + x + b) (sym (idr+ a)) ⟩
  a + (a + 0) + b ∎

p2 : (a b c : ℕ) → c * (b + 1 + a) ≡ a * c + b * c + c
p2 a b c =
  c * (b + 1 + a)
  ≡⟨ dist*+ c (b + 1) a ⟩
  c * (b + 1) + c * a
  ≡⟨ cong (_+ c * a) (dist*+ c b 1) ⟩
  c * b + c * 1 + c * a
  ≡⟨ comm+ (c * b + c * 1) (c * a) ⟩
  c * a + (c * b + c * 1)
  ≡⟨ cong₃ (λ x y z → x + (y + z)) (comm* c a) (comm* c b) (idr* c) ⟩
  a * c + (b * c + c)
  ≡⟨ sym (assoc+ (a * c) (b * c) c) ⟩
  a * c + b * c + c ∎

-- \==n = ≢
-- x ≢ y = ¬ (x ≡ y) = (x ≡ y) → ⊥

p9' : 0 ≢ the ℕ 1
p9' ()

p9 : 2 * 2 ≢ 3 * 1
p9 ()

-- Egyszerűbb, amikor mondani kell egy ellenpéldát:
p10 : ¬ ((n : ℕ) → n + 2 ≡ n + 1)
p10 f with f 0
... | ()

suc-inj : {x y : ℕ} → suc x ≡ suc y → x ≡ y
suc-inj refl = refl

-- ...mintsem bizonyítani, hogy ez a kettő sosem lesz egyenlő:
p11 : (n : ℕ) → n + 2 ≢ n + 1
p11 (suc n) e = p11 n (suc-inj e)

-- Mókásabb helyzet.
p11'' : ¬ Σ ℕ (λ n → n + 3 ≡ n + 1)
p11'' = f p11' where
  f : ((n : ℕ) → n + 3 ≢ n + 1) → ¬ Σ ℕ (λ n → n + 3 ≡ n + 1)
  f h (n , e) = h n e
  p11' : (n : ℕ) → n + 3 ≢ n + 1
  p11' (suc n) e = p11' n (suc-inj e)

p12 : ¬ Σ ℕ (λ n → n + n ≡ 3)
p12 (suc (suc (suc zero)) , ())
p12 (suc (suc (suc (suc n))) , ())

[m+n]^2=m^2+2mn+n^2 : (m n : ℕ) → (m + n) * (m + n) ≡ m * m + 2 * m * n + n * n
[m+n]^2=m^2+2mn+n^2 m n = {!!}

{-
infixr 8 _^_
_^_ : ℕ → ℕ → ℕ
x ^ zero  = 1
x ^ suc n = x * x ^ n
-}

p1 : (a b : ℕ) → (a + b) ^ 2 ≡ a ^ 2 + 2 * a * b + b ^ 2
p1 a b = {!!}

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
