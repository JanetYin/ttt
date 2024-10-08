open import lib

---------------------------------------------------------
-- library
------------------------------------------------------

sym : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀{i j}{A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y
subst P refl p = p

_≡⟨_⟩_ : ∀{i}{A : Set i}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = trans p q

-- \qed = ∎
_∎ : ∀{i}{A : Set i}(x : A) → x ≡ x
_ ∎ = refl

infixr 2 _≡⟨_⟩_
infix 3 _∎

ass+ : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
ass+ zero    b c = refl
ass+ (suc a) b c = cong suc (ass+ a b c)

idr+ : (a : ℕ) → a + 0 ≡ a
idr+ zero    = refl
idr+ (suc a) = cong suc (idr+ a)

sucr+ : (a b : ℕ) → a + suc b ≡ suc a + b
sucr+ zero    b = refl
sucr+ (suc a) b = cong suc (sucr+ a b)

comm+ : (a b : ℕ) → a + b ≡ b + a
comm+ zero b = sym (idr+ b)
comm+ (suc a) b = trans (cong suc (comm+ a b)) (sym (sucr+ b a))

dist+* : (m n o : ℕ) → (n + o) * m ≡ n * m + o * m
dist+* m zero o = refl
dist+* m (suc n) o = trans (cong (m +_) (dist+* m n o)) (sym (ass+ m (n * m) (o * m)))

dist*+ : (m n o : ℕ) → m * (n + o) ≡ m * n + m * o
dist*+ zero n o = refl
dist*+ (suc m) n o =
  n + o + m * (n + o)
  ≡⟨ cong (n + o +_) (dist*+ m n o) ⟩
  (n + o) + (m * n + m * o)
  ≡⟨ ass+ n o (m * n + m * o) ⟩
  n + (o + (m * n + m * o))
  ≡⟨ cong (n +_) (sym (ass+ o (m * n) (m * o))) ⟩
  n + (o + m * n + m * o)
  ≡⟨ cong (λ x → n + (x + m * o)) (comm+ o (m * n)) ⟩
  n + (m * n + o + m * o)
  ≡⟨ cong (n +_) (ass+ (m * n) o (m * o)) ⟩
  n + (m * n + (o + m * o))
  ≡⟨ sym (ass+ n (m * n) (o + m * o)) ⟩
  n + m * n + (o + m * o) ∎

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

--------------------------------------------------------
-- Hatványozás
--------------------------------------------------------

infixr 8 _^_
_^_ : ℕ → ℕ → ℕ
a ^ zero = 1
a ^ suc n = a * a ^ n

0^ : (n : ℕ) → 0 ^ (suc n) ≡ 0
0^ n = refl

^0 : (a : ℕ) → a ^ 0 ≡ 1
^0 a = refl

1^ : (n : ℕ) → 1 ^ n ≡ 1
1^ zero = refl
1^ (suc n) = cong (_+ 0) (1^ n)

^1 : (a : ℕ) → a ^ 1 ≡ a
^1 = idr*

^+ : (m n o : ℕ) → m ^ (n + o) ≡ m ^ n * m ^ o
^+ m zero o = sym (idr+ (m ^ o))
^+ m (suc n) o = trans (cong (m *_) (^+ m n o)) (sym (ass* m (m ^ n) (m ^ o)))

^* : (a m n : ℕ) → a ^ (m * n) ≡ (a ^ m) ^ n
^* a 0 n = sym (1^ n)
^* a (suc m) zero = cong (a ^_) (nullr* m)
^* a (suc m) (suc n) =
  a * a ^ (n + m * suc n)
  ≡⟨ cong (a *_) (^+ a n (m * suc n)) ⟩
  a * (a ^ n * a ^ (m * suc n))
  ≡⟨ cong (λ x → a * (a ^ n * x)) (^* a m (suc n)) ⟩
  a * (a ^ n * (a ^ m * (a ^ m) ^ n))
  ≡⟨ cong (λ x → a * (a ^ n * (a ^ m * x))) (sym (^* a m n)) ⟩
  a * (a ^ n * (a ^ m * a ^ (m * n)))
  ≡⟨ {!   !} ⟩
  {!   !}
  ≡⟨ {!   !} ⟩
  {!   !}
  ≡⟨ {!   !} ⟩
  a * a ^ m * (a ^ n * a ^ (m * n))
  ≡⟨ cong (a * a ^ m *_) (sym (^+ a n (m * n))) ⟩
  a * a ^ m * a ^ (n + m * n)
  ≡⟨ cong (a ^ suc m *_) (^* a (suc m) n) ⟩
  a ^ suc m * (a ^ suc m) ^ n ∎

*^ : (a b n : ℕ) → (a * b) ^ n ≡ a ^ n * b ^ n
*^ a b n = {!   !}

---------------------------------------------------------
-- equational reasoning
------------------------------------------------------

Dec : ∀{i} → Set i → Set i
Dec A = A ⊎ ¬ A

[m+n]^2=m^2+2mn+n^2 : (m n : ℕ) → (m + n) * (m + n) ≡ m * m + 2 * m * n + n * n
[m+n]^2=m^2+2mn+n^2 = {!!}

p1 : (a b : ℕ) → (a + b) ^ 2 ≡ a ^ 2 + 2 * a * b + b ^ 2
p1 = {!!}

p2 : (a b c : ℕ) → c * (b + 1 + a) ≡ a * c + b * c + c
p2 = {!!}

p3 : (a b : ℕ) → a + a + b + a * 0 ≡ 2 * a + b
p3 = {!!}

p4 : (x y : ℕ) → ((x + (y + zero)) + x) ≡ (2 * x + y)
p4 = {!!}









