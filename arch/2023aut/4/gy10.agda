open import Lib

---------------------------------------------------------
-- equational reasoning
------------------------------------------------------

{-
-- tranzitivitás, csak átláthatóbban:

-- \== = ≡
-- \< = ⟨
-- \> = ⟩
_≡⟨_⟩_ : ∀{i}{A : Set i}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = trans p q

-- \qed = ∎
_∎ : ∀{i}{A : Set i}(x : A) → x ≡ x
_ ∎ = refl

infixr 2 _≡⟨_⟩_
infix 3 _∎
-}

p4 : (x y : ℕ) → ((x + (y + zero)) + x) ≡ (2 * x + y)
p4 x y = x + (y + zero) + x
    ≡⟨ cong (λ a → x + a + x) (idr+ y) ⟩
    x + y + x
    ≡⟨ ass+ x y x ⟩
    x + (y + x)
    ≡⟨ cong (λ a → x + a) (comm+ y x) ⟩
    x + (x + y)
    ≡⟨ sym (ass+ x x y) ⟩
    x + x + y
    ≡⟨ cong (λ a → x + a + y) (sym (idr+ x)) ⟩
    x + (x + zero) + y ∎

p3 : (a b : ℕ) → a + a + b + a * 0 ≡ 2 * a + b
p3 a b = a + a + b + a * 0
    ≡⟨ cong (λ x → a + a + b + x) (nullr* a) ⟩
    a + a + b + zero
    ≡⟨ idr+ (a + a + b) ⟩
    a + a + b
    ≡⟨ cong (λ x → a + x + b) (sym (idr+ a)) ⟩
    a + (a + zero) + b ∎

p2 : (a b c : ℕ) → c * (b + 1 + a) ≡ a * c + b * c + c
p2 = {!!}

[m+n]^2=m^2+2mn+n^2 : (m n : ℕ) → (m + n) * (m + n) ≡ m * m + 2 * m * n + n * n
[m+n]^2=m^2+2mn+n^2 = {!!}

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
0^ n = refl

^0 : (a : ℕ) → a ^' 0 ≡ 1
^0 a = refl

1^ : (n : ℕ) → 1 ^' n ≡ 1
1^ zero = refl
1^ (suc n) = cong (λ x → x + zero) (1^ n)

^1 : (a : ℕ) → a ^' 1 ≡ a
^1 a = idr* a

^+ : (a m n : ℕ) → a ^' (m + n) ≡ a ^' m * a ^' n
^+ a zero n = sym (idr+ (a ^' n))
^+ a (suc m) n = trans (cong (λ x → a * x) (^+ a m n)) (sym (ass* a (a ^' m) (a ^' n)))

*^ : (a b n : ℕ) → (a * b) ^' n ≡ a ^' n * b ^' n
*^ a b zero = refl
*^ a b (suc n) = a * b * (a * b) ^' n
        ≡⟨ cong (λ x → a * b * x) (*^ a b n) ⟩
        a * b * (a ^' n * b ^' n)
        ≡⟨ sym (ass* (a * b) (a ^' n) ( b ^' n)) ⟩
        a * b * a ^' n * b ^' n
        ≡⟨ cong (λ x → x * b ^' n) (ass* a b (a ^' n)) ⟩
        a * (b * a ^' n) * b ^' n
        ≡⟨ cong (λ x → a * x * b ^' n) (comm* b (a ^' n)) ⟩
        a * (a ^' n * b) * b ^' n
        ≡⟨ cong (λ x → x * b ^' n) (sym (ass* a (a ^' n) b)) ⟩
        a * a ^' n * b * b ^' n
        ≡⟨ ass* (a * a ^' n) b (b ^' n) ⟩
        a * a ^' n * (b * b ^' n) ∎

^* : (a m n : ℕ) → a ^' (m * n) ≡ (a ^' m) ^' n
^* a m n = {!   !}
 