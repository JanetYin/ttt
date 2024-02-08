module gy11 where

open import Lib

---------------------------------------------------------
-- equational reasoning
------------------------------------------------------

p4 : (x y : ℕ) → ((x + (y + zero)) + x) ≡ (2 * x + y)
p4 x y = 
  (x + (y + zero)) + x ≡⟨ ass+ x (y + zero) x ⟩
  x + ((y + zero) + x) ≡⟨ cong (x +_) (comm+ (y + 0) x) ⟩
  x + (x + (y + 0))    ≡⟨ cong (λ a → x + (x + a)) (comm+ y 0) ⟩
  x + (x + (0 + y))    ≡⟨ cong (x +_) (sym (ass+ x 0 y)) ⟩
  x + ((x + 0) + y)    ≡⟨ sym (ass+ x (x + zero) y) ⟩
  x + (x + zero) + y   ≡⟨ refl ⟩
  2 * x + y ∎ 

p3 : (a b : ℕ) → a + a + b + a * 0 ≡ 2 * a + b
p3 a b = 
  a + a + b + a * 0
  ≡⟨ cong (λ x → a + a + b + x) (nullr* a) ⟩
  a + a + b + 0
  ≡⟨ idr+ (a + a + b) ⟩
  a + a + b
  ≡⟨ cong (λ x → a + x + b) (sym (idr+ a)) ⟩
  a + (a + 0) + b
  ≡⟨ refl ⟩
  2 * a + b ∎

p2 : (a b c : ℕ) → c * (b + 1 + a) ≡ a * c + b * c + c
p2 a b c =
  c * ((b + 1) + a)
  ≡⟨ dist*+ c (b + 1) a ⟩
  c * (b + 1) + c * a
  ≡⟨ cong (_+ c * a) (dist*+ c b 1) ⟩
  c * b + c * 1 + c * a
  ≡⟨ cong₃ (λ x y z → x + y + z) (comm* c b) (idr* c) (comm* c a) ⟩ -- \_3 = ₃
  b * c + c + a * c
  ≡⟨ comm+ (b * c + c) (a * c) ⟩
  a * c + (b * c + c)
  ≡⟨ sym (ass+ (a * c) (b * c) c) ⟩
  a * c + b * c + c ∎

{-
infixr 8 _^'_
_^'_ : ℕ → ℕ → ℕ
x ^' zero  = 1
x ^' suc n = x * x ^' n

infixr 8 _^_
_^_ : (x y : ℕ) → .⦃ y + x ≢ℕ 0 ⦄ → ℕ
x ^ zero = 1
x ^ suc zero = x
x ^ suc (suc y) = x * (x ^ suc y)

-- A vesszős definíciót érdemes használni.
-- A simáról nehéz állításokat bizonyítani.
-}

0^ : (n : ℕ) → 0 ^' (suc n) ≡ 0
0^ _ = refl

^0 : (a : ℕ) → a ^' 0 ≡ 1
^0 _ = refl

1^ : (n : ℕ) → 1 ^' n ≡ 1
1^ zero = refl
1^ (suc n) = let ih = 1^ n in cong (_+ 0) ih

^1 : (a : ℕ) → a ^' 1 ≡ a
^1 = idr*

^+ : (a m n : ℕ) → a ^' (m + n) ≡ a ^' m * a ^' n
^+ a zero n = sym (idr+ (a ^' n))
^+ a (suc m) n =
  a * a ^' (m + n)
  ≡⟨ cong (a *_) (^+ a m n) ⟩
  a * (a ^' m * a ^' n)
  ≡⟨ sym (ass* a (a ^' m) (a ^' n)) ⟩
  a * a ^' m * a ^' n ∎

^* : (a m n : ℕ) → a ^' (m * n) ≡ (a ^' m) ^' n
^* a zero n = sym (1^ n)
^* a (suc m) n = 
  a ^' (n + m * n)
  ≡⟨ ^+ a n (m * n) ⟩
  a ^' n * a ^' (m * n)
  ≡⟨ cong (a ^' n *_) (^* a m n) ⟩
  a ^' n * (a ^' m) ^' n
  ≡⟨ {!   !} ⟩
  {!   !}
  ≡⟨ {!   !} ⟩
  (a * a ^' m) ^' n
  ≡⟨ refl ⟩
  (a ^' suc m) ^' n ∎

*^ : (a b n : ℕ) → (a * b) ^' n ≡ a ^' n * b ^' n
*^ = {!!}

p1 : (a b : ℕ) → (a + b) ^' 2 ≡ a ^' 2 + 2 * a * b + b ^' 2
p1 = {!!}