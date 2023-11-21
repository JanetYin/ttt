open import Lib

---------------------------------------------------------
-- equational reasoning
------------------------------------------------------

p4 : (x y : ℕ) → ((x + (y + zero)) + x) ≡ (2 * x + y)
p4 x y = trans (ass+ x _ _ ) (trans (cong (x +_) (trans (trans (ass+ y _ _) (comm+ y _)) (sym (ass+ x _ _)))) (sym (ass+ x _ _)))

p3 : (a b : ℕ) → a + a + b + a * 0 ≡ 2 * a + b
p3 a b = trans (cong (a + a + b +_) (nullr* a)) (trans (idr+ _) (cong (λ x → a + x + b) (sym (idr+ a))))

p2 : (a b c : ℕ) → c * (b + 1 + a) ≡ a * c + b * c + c
p2 a b c = trans (cong (λ x → c * (x + a)) (trans (sucr+ b _) (cong suc (idr+ b)))) (trans (comm* c _) (trans (comm+ c _) (cong (_+ c) (trans (dist+* b _ _) (comm+ (b * c) _)))))

[m+n]^2=m^2+2mn+n^2 : (m n : ℕ) → (m + n) * (m + n) ≡ m * m + 2 * m * n + n * n
[m+n]^2=m^2+2mn+n^2 m n = trans (trans (dist+* m _ _) (trans (cong₂ (λ x y → x + y) {m * (m + n)} (trans (comm* m _) (dist+* m _ _)) (trans (comm* n _) (dist+* m _ _))) (trans (cong (λ x → m * m + n * m + (x + n * n)) (comm* m _)) (trans (ass+ (m * m) (n * m) _) (trans (cong (m * m +_) (sym (ass+ (n * m) (n * m) (n * n)))) (trans (sym (ass+ (m * m) (n * m + n * m) (n * n))) (cong (_+ n * n) (cong (m * m +_) (trans (cong₂ _+_ (comm* n _) (comm* n _)) (sym (dist+* m m n))))))))))) (cong (λ x → m * m + (m + x) * n + n * n) (sym (idr+ m)))

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

p1 : (a b : ℕ) → (a + b) ^' 2 ≡ a ^' 2 + 2 * a * b + b ^' 2
p1 = {!!}

0^ : (n : ℕ) → 0 ^' (suc n) ≡ 0
0^ = {!!}

^0 : (a : ℕ) → a ^' 0 ≡ 1
^0 = {!!}

1^ : (n : ℕ) → 1 ^' n ≡ 1
1^ = {!!}

^1 : (a : ℕ) → a ^' 1 ≡ a
^1 = {!!}

^+ : (a m n : ℕ) → a ^' (m + n) ≡ a ^' m * a ^' n
^+ = {!!}

^* : (a m n : ℕ) → a ^' (m * n) ≡ (a ^' m) ^' n
^* = {!!}

*^ : (a b n : ℕ) → (a * b) ^' n ≡ a ^' n * b ^' n
*^ = {!!}
