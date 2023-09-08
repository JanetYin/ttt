open import lib

---------------------------------------------------------
-- library
------------------------------------------------------

sym : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

infix  3 _∎
infixr 2 _≡⟨_⟩_
-- \< \> \==

_≡⟨_⟩_ : ∀{i}{A : Set i}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

_∎ : ∀{i}{A : Set i}(a : A) → a ≡ a
a ∎ = refl
-- \qed

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀{i j}{A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y
subst P refl p = p

ass+ : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
ass+ zero    b c = refl
ass+ (suc a) b c = cong suc (ass+ a b c)

idr+ : (a : ℕ) → a + 0 ≡ a
idr+ zero    = refl
idr+ (suc a) = cong suc (idr+ a)

+suc : (a b : ℕ) → suc a + b ≡ a + suc b
+suc zero    b = refl
+suc (suc a) b = cong suc (+suc a b)

comm+ : (a b : ℕ) → a + b ≡ b + a
comm+ zero b = sym (idr+ b)
comm+ (suc a) b = trans (cong suc (comm+ a b)) (+suc b a)

dist+* : (m n o : ℕ) → (n + o) * m ≡ n * m + o * m
dist+* m zero o = refl
dist+* m (suc n) o = trans (cong (m +_) (dist+* m n o)) (sym (ass+ m (n * m) (o * m)))

nullr* : (n : ℕ) → n * 0 ≡ 0
nullr* zero = refl
nullr* (suc n) = nullr* n

idl* : (n : ℕ) → 1 * n ≡ n
idl* n = idr+ n

idr* : (n : ℕ) → n * 1 ≡ n
idr* zero = refl
idr* (suc n) = cong suc (idr* n)

ass* : (m n o : ℕ) → (m * n) * o ≡ m * (n * o)
ass* zero n o = refl
ass* (suc m) n o = trans (dist+* o n (m * n)) (cong (n * o +_) (ass* m n o))

comm*-helper : (n m : ℕ) → n + n * m ≡ n * suc m
comm*-helper zero m = refl
comm*-helper (suc n) m = trans (cong suc (trans (sym (ass+ n m (n * m))) (trans (cong (_+ n * m) (comm+ n m)) (ass+ m n (n * m))))) (cong (λ z → suc (m + z)) (comm*-helper n m))

comm* : (m n : ℕ) → m * n ≡ n * m
comm* zero n = sym (nullr* n)
comm* (suc m) n = trans (cong (n +_) (comm* m n)) (comm*-helper n m)

---------------------------------------------------------
-- equational reasoning
------------------------------------------------------

p4 : (x y : ℕ) → ((x + (y + zero)) + x) ≡ (2 * x + y)
p4 x y = x + (y + zero) + x 
        ≡⟨ cong (λ a → x + a + x) (idr+ y) ⟩ 
        x + y + x
        ≡⟨ comm+ (x + y) x ⟩ 
        x + (x + y)
        ≡⟨ sym (ass+ x x y) ⟩
        x + x + y
        ≡⟨ cong (λ a → x + a + y) (sym (idr+ x)) ⟩
        x + (x + zero) + y ∎

p3 : (a b : ℕ) → a + a + b + a * 0 ≡ 2 * a + b
p3 a b = a + a + b + a * zero 
        ≡⟨ cong (λ x → a + a + b + x) (nullr* a) ⟩ 
        a + a + b + zero
        ≡⟨ idr+ (a + a + b) ⟩ 
        a + a + b
        ≡⟨ cong (λ x → a + x + b) (sym (idr+ a)) ⟩
        a + (a + zero) + b
        ≡⟨ refl ⟩ 
        a + (a + zero) + b
        ≡⟨ refl ⟩ 
        a + (a + zero) + b
        ≡⟨ refl ⟩ 
        a + (a + zero) + b ∎

p2 : (a b c : ℕ) → c * (b + 1 + a) ≡ a * c + b * c + c
p2 a b c = c * (b + 1 + a) 
        ≡⟨ comm* c (b + 1 + a) ⟩ 
        (b + 1 + a) * c
        ≡⟨ dist+* c (b + 1) a ⟩ 
        (b + 1) * c + a * c
        ≡⟨ cong (λ x → x + a * c) (dist+* c b 1) ⟩ 
        b * c + (c + zero) + a * c
        ≡⟨ cong (λ x → b * c + x + a * c) (idr+ c) ⟩ 
        b * c + c + a * c
        ≡⟨ comm+ (b * c + c) (a * c) ⟩
        a * c + (b * c + c)
        ≡⟨ sym (ass+ (a * c) (b * c) c) ⟩
        a * c + b * c + c ∎

[m+n]^2=m^2+2mn+n^2 : (m n : ℕ) → (m + n) * (m + n) ≡ m * m + 2 * m * n + n * n
[m+n]^2=m^2+2mn+n^2 m n = 
    (m + n) * (m + n) 
    ≡⟨ dist+* (m + n) m n ⟩ 
    m * (m + n) + n * (m + n)
    ≡⟨ cong (λ a → a + n * (m + n)) (comm* m (m + n)) ⟩ 
    (m + n) * m + n * (m + n)
    ≡⟨ cong (λ a → a + n * (m + n)) (dist+* m m n) ⟩ 
    m * m + n * m + n * (m + n)
    ≡⟨ cong (λ a → m * m + n * m + a) (comm* n (m + n)) ⟩ 
    m * m + n * m + (m + n) * n
    ≡⟨ cong (λ a → m * m + n * m + a) (dist+* n m n) ⟩ 
    m * m + n * m + (m * n + n * n)
    ≡⟨ ass+ (m * m) (n * m) (m * n + n * n) ⟩ 
    m * m + (n * m + (m * n + n * n))
    ≡⟨ cong (λ a → m * m + a) (sym (ass+ (n * m) (m * n) (n * n))) ⟩ 
    m * m + (n * m + m * n + n * n)
    ≡⟨ sym (ass+ (m * m) (n * m + m * n) (n * n)) ⟩ 
    m * m + (n * m + m * n) + n * n
    ≡⟨ cong (λ a → m * m + (a + m * n) + n * n) (comm* n m) ⟩
    m * m + (m * n + m * n) + n * n
    ≡⟨ cong (λ a → m * m + a + n * n) (sym (dist+* n m m)) ⟩
    m * m + (m + m) * n + n * n
    ≡⟨ cong (λ a → m * m + (m + a) * n + n * n) (sym (idr+ m)) ⟩
    m * m + (m + (m + zero)) * n + n * n ∎

_^_ : ℕ → ℕ → ℕ
a ^ zero = suc zero
a ^ suc n = a * (a ^ n)
infixl 9 _^_

p1 : (a b : ℕ) → (a + b) ^ 2 ≡ a ^ 2 + 2 * a * b + b ^ 2
p1 a b = (a + b) * ((a + b) * 1) 
        ≡⟨ cong (λ x → (a + b) * x) (idr* (a + b)) ⟩ 
        (a + b) * (a + b)
        ≡⟨ [m+n]^2=m^2+2mn+n^2 a b ⟩ 
        a * a + (a + (a + zero)) * b + b * b
        ≡⟨ cong (λ x → (a * x) + (a + (a + zero)) * b + b * b) (sym (idr* a)) ⟩ 
        a * (a * 1) + (a + (a + zero)) * b + b * b
        ≡⟨ cong (λ x → a * (a * 1) + (a + (a + zero)) * b + b * x) (sym (idr* b)) ⟩ 
        a * (a * 1) + (a + (a + zero)) * b + b * (b * 1) ∎

0^ : (n : ℕ) → 0 ^ (suc n) ≡ 0
0^ n = refl

^0 : (a : ℕ) → a ^ 0 ≡ 1
^0 a = refl

1^ : (n : ℕ) → 1 ^ n ≡ 1
1^ zero = refl
1^ (suc n) = trans (idr+ (1 ^ n)) (1^ n)

^1 : (a : ℕ) → a ^ 1 ≡ a
^1 a = idr* a

^+ : (a x y : ℕ) → a ^ (x + y) ≡ a ^ x * a ^ y
^+ a zero y = sym (idr+ (a ^ y))
^+ a (suc x) y = trans (cong (λ b → a * b) (^+ a x y)) (sym (ass* a (a ^ x) (a ^ y)))

*^ : (a b n : ℕ) → (a * b) ^ n ≡ a ^ n * b ^ n
*^ a b zero = refl
*^ a b (suc n) = a * b * (a * b) ^ n 
        ≡⟨ cong (λ z → a * b * z) (*^ a b n) ⟩
        a * b * (a ^ n * b ^ n)
        ≡⟨ ass* a b (a ^ n * b ^ n) ⟩
        a * (b * (a ^ n * b ^ n))
        ≡⟨ cong (λ z → a * z) (sym (ass* b (a ^ n) (b ^ n))) ⟩
        a * (b * a ^ n * b ^ n)
        ≡⟨ cong (λ z → a * (z * (b ^ n))) (comm* b (a ^ n)) ⟩
        a * (a ^ n * b * b ^ n)
        ≡⟨ sym (ass* a (a ^ n * b) (b ^ n)) ⟩
        a * (a ^ n * b) * b ^ n
        ≡⟨ cong (λ z → z * (b ^ n)) (sym (ass* a (a ^ n) b)) ⟩
        a * a ^ n * b * b ^ n
        ≡⟨ ass* (a * (a ^ n)) b (b ^ n) ⟩
        a * a ^ n * (b * b ^ n) ∎

^* : (a x y : ℕ) → a ^ (x * y) ≡ (a ^ x) ^ y
^* a zero y = sym (1^ y)
^* a (suc x) zero = cong (λ z → a ^ z) (nullr* x)
^* zero (suc x) (suc y) = refl
^* (suc a) (suc x) (suc y) = suc a ^ (y + x * suc y) + a * suc a ^ (y + x * suc y) 
        ≡⟨ refl ⟩
        suc a * suc a ^ (y + x * suc y) 
        ≡⟨ cong (λ z → suc a * z) (^+ (suc a) y (x * suc y)) ⟩
        suc a * (suc a ^ y * suc a ^ (x * suc y))
        ≡⟨ sym (ass* (suc a) (suc a ^ y) (suc a ^ (x * suc y))) ⟩
        (suc a * suc a ^ y) * suc a ^ (x * suc y)
        ≡⟨ cong (λ z → (suc a * suc a ^ y) * z) (^* (suc a) x (suc y)) ⟩
        (suc a * suc a ^ y) * (suc a ^ x * suc a ^ x ^ y)
        ≡⟨ refl ⟩
        (suc a ^ (suc y)) * (suc a ^ x ^ (suc y))
        ≡⟨ sym (*^ (suc a) (suc a ^ x) (suc y)) ⟩
        (suc a * suc a ^ x) ^ (suc y)
        ≡⟨ refl ⟩
        (suc a ^ x + a * suc a ^ x) ^ (suc y)
        ≡⟨ refl ⟩
        (suc a ^ x + a * suc a ^ x) * (suc a ^ x + a * suc a ^ x) ^ y ∎
