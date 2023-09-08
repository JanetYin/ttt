module proofs where

open import lib

sym : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq2 = eq2

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀{i j k}{A : Set i}{B : Set j}{C : Set k}(f : A → B → C){x x' : A}{y y' : B} →
  x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

cong₃ : ∀{i j k l}{A : Set i}{B : Set j}{C : Set k}{D : Set l}(f : A → B → C → D){x x' : A}{y y' : B}{z z' : C} →
  x ≡ x' → y ≡ y' → z ≡ z' → f x y z ≡ f x' y' z'
cong₃ f refl refl refl = refl

cong∘ : ∀{i j}{A : Set i}{B : Set j}(f : B → A)(g : A → B) →
  {a b : A}(eq : a ≡ b) → cong f (cong g eq) ≡ cong (λ x → f (g x)) eq
cong∘ f g refl = refl

cong-id : ∀{i}{A : Set i}{a b : A} →
  (eq : a ≡ b) → cong (λ x → x) eq ≡ eq
cong-id refl = refl

subst : ∀{i j}{A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y
subst P refl px = px

substconst  : ∀{ℓ}{A : Set ℓ}{ℓ'}{B : Set ℓ'}{a a' : A}(e : a ≡ a'){b : B} →
  subst (λ _ → B) e b ≡ b
substconst refl = refl

substcong : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}(C : B → Set ℓ'')(f : A → B) → 
  {a a' : A}(e : a ≡ a'){c : C (f a)} → 
  subst {A = B} C (cong f e) c ≡ subst {A = A} (λ a → C (f a)) e c
substcong C f refl = refl

substΠ : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}(C : A → B → Set ℓ'') →
  {a a' : A}(e : a ≡ a'){f : (b : B) → C a b} → 
  subst (λ a → (b : B) → C a b) e f ≡ λ b → subst (λ a → C a b) e (f b)
substΠ C refl = refl

substsubst : ∀{ℓ}{A : Set ℓ}{ℓ'}(P : A → Set ℓ'){a a' a'' : A}(e : a ≡ a')(e' : a' ≡ a''){p : P a} →
  subst P e' (subst P e p) ≡ subst P (trans e e') p
substsubst P refl refl = refl

subst→' : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : Set ℓ'}(C : A → Set ℓ''){a a' : A}(e : a ≡ a'){f : B → C a} → 
  subst (λ a → B → C a) e f ≡ λ b → subst C e (f b)
subst→' C refl = refl

subst$ : ∀{ℓ ℓ' ℓ''}{A : Set ℓ}{B : A → Set ℓ'}{C : A → Set ℓ''}
  (f : ∀ a → B a → C a){a a' : A}(e : a ≡ a'){b : B a} → 
  f a' (subst B e b) ≡ subst C e (f a b) 
subst$ f refl = refl

_≡⟨_⟩_ : ∀{i}{A : Set i}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = trans p q

_∎ : ∀{i}{A : Set i}(x : A) → x ≡ x
_ ∎ = refl

infixr 2 _≡⟨_⟩_
infix 3 _∎

idr+ : (n : ℕ) → n + zero ≡ n
idr+ zero = refl
idr+ (suc n) = cong suc (idr+ n)

sucr+ : (n m : ℕ) → n + suc m ≡ suc (n + m)
sucr+ zero m = refl
sucr+ (suc n) m = cong suc (sucr+ n m)

ass+ : (m n o : ℕ) → (m + n) + o ≡ m + (n + o)
ass+ zero n o = refl
ass+ (suc m) n o = cong suc (ass+ m n o)

comm+ : (m n : ℕ) → m + n ≡ n + m
comm+ zero n = sym (idr+ n)
comm+ (suc m) n = trans (cong suc (comm+ m n)) (sym (sucr+ n m))

dist+* : (m n o : ℕ) → (m + n) * o ≡ m * o + n * o
dist+* zero n o = refl
dist+* (suc m) n o = trans (cong (o +_) (dist+* m n o)) (sym (ass+ o (m * o) (n * o)))

dist*+ : (m n o : ℕ) → m * (n + o) ≡ m * n + m * o
dist*+ zero n o = refl
dist*+ (suc m) n o =
  n + o + m * (n + o)
  ≡⟨ ass+ n o (m * (n + o)) ⟩
  n + (o + m * (n + o)) 
  ≡⟨ cong (n +_) (comm+ o (m * (n + o))) ⟩
  n + (m * (n + o) + o)
  ≡⟨ sym (ass+ n (m * (n + o)) o) ⟩
  n + m * (n + o) + o
  ≡⟨ cong (λ x → n + x + o) (dist*+ m n o) ⟩
  n + (m * n + m * o) + o
  ≡⟨ cong (_+ o) (sym (ass+ n (m * n) (m * o))) ⟩
  n + m * n + m * o + o
  ≡⟨ ass+ (n + m * n) (m * o) o ⟩
  n + m * n + (m * o + o)
  ≡⟨ cong ((n + m * n) +_) (comm+ (m * o) o) ⟩
  n + m * n + (o + m * o) ∎

nullr* : (n : ℕ) → n * 0 ≡ 0
nullr* zero = refl
nullr* (suc n) = nullr* n

idl* : (n : ℕ) → 1 * n ≡ n
idl* = idr+ 

idr* : (n : ℕ) → n * 1 ≡ n
idr* zero = refl
idr* (suc n) = cong suc (idr* n)

sucr* : (n m : ℕ) → n * suc m ≡ n + n * m
sucr* zero m = refl
sucr* (suc n) m =
  suc (m + n * suc m)
  ≡⟨ cong suc (comm+ m (n * suc m)) ⟩
  suc (n * suc m + m)
  ≡⟨ cong (λ x → suc (x + m)) (sucr* n m) ⟩
  suc (n + n * m + m)
  ≡⟨ cong suc (ass+ n (n * m) m) ⟩
  suc (n + (n * m + m))
  ≡⟨ cong (λ x → suc (n + x)) (comm+ (n * m) m) ⟩
  suc (n + (m + n * m)) ∎

ass* : (m n o : ℕ) → (m * n) * o ≡ m * (n * o)
ass* zero n o = refl
ass* (suc m) n o =
  (n + m * n) * o
  ≡⟨ dist+* n (m * n) o ⟩
  n * o + m * n * o 
  ≡⟨ cong (n * o +_) (ass* m n o) ⟩
  n * o + m * (n * o) ∎

comm* : (m n : ℕ) → m * n ≡ n * m
comm* zero n = sym (nullr* n)
comm* (suc m) n =
  n + m * n
  ≡⟨ cong (n +_) (comm* m n) ⟩
  n + n * m
  ≡⟨ sym (sucr* n m) ⟩
  n * suc m ∎

infixr 8 _^_
_^_ : ℕ → ℕ → ℕ
a ^ zero = 1
a ^ suc n = a * a ^ n

nulll^ : (n : ℕ) → 1 ^ n ≡ 1
nulll^ zero = refl
nulll^ (suc n) = cong (_+ 0) (nulll^ n)

idr^ : (a : ℕ) → a ^ 1 ≡ a
idr^ = idr*

dist^+ : (m n o : ℕ) → m ^ (n + o) ≡ m ^ n * m ^ o
dist^+ m zero o = sym (idr+ (m ^ o))
dist^+ m (suc n) o = trans (cong (m *_) (dist^+ m n o)) (sym (ass* m (m ^ n) (m ^ o)))

dist^* : (a m n : ℕ) → a ^ (m * n) ≡ (a ^ m) ^ n
dist^* a 0 n = sym (nulll^ n)
dist^* a (suc m) zero = cong (a ^_) (nullr* m)
dist^* a (suc m) (suc n) =
  a * a ^ (n + m * suc n)
  ≡⟨ cong (a *_) (dist^+ a n (m * suc n)) ⟩
  a * (a ^ n * a ^ (m * suc n))
  ≡⟨ cong (λ x → a * (a ^ n * x)) (dist^* a m (suc n)) ⟩
  a * (a ^ n * (a ^ m * (a ^ m) ^ n))
  ≡⟨ cong (λ x → a * (a ^ n * (a ^ m * x))) (sym (dist^* a m n)) ⟩
  a * (a ^ n * (a ^ m * a ^ (m * n)))
  ≡⟨ cong (a *_) (sym (ass* (a ^ n) (a ^ m) (a ^ (m * n)))) ⟩
  a * (a ^ n * a ^ m * a ^ (m * n))
  ≡⟨ cong (λ x → a * (x * a ^ (m * n))) (comm* (a ^ n) (a ^ m)) ⟩
  a * (a ^ m * a ^ n * a ^ (m * n))
  ≡⟨ cong (a *_) (ass* (a ^ m) (a ^ n) (a ^ (m * n))) ⟩
  a * (a ^ m * (a ^ n * a ^ (m * n)))
  ≡⟨ sym (ass* a (a ^ m) (a ^ n * a ^ (m * n))) ⟩
  a * a ^ m * (a ^ n * a ^ (m * n))
  ≡⟨ cong (a * a ^ m *_) (sym (dist^+ a n (m * n))) ⟩
  a * a ^ m * a ^ (n + m * n)
  ≡⟨ cong (a ^ suc m *_) (dist^* a (suc m) n) ⟩
  a ^ suc m * (a ^ suc m) ^ n ∎

dist*^ : (a b n : ℕ) → (a * b) ^ n ≡ a ^ n * b ^ n
dist*^ a b zero = refl
dist*^ a b (suc n) =
  a * b * (a * b) ^ n
  ≡⟨ cong (a * b *_) (dist*^ a b n) ⟩
  a * b * (a ^ n * b ^ n)
  ≡⟨ ass* a b (a ^ n * b ^ n) ⟩
  a * (b * (a ^ n * b ^ n))
  ≡⟨ cong (a *_) (sym (ass* b (a ^ n) (b ^ n))) ⟩
  a * (b * a ^ n * b ^ n)
  ≡⟨ cong (λ x → a * (x * b ^ n)) (comm* b (a ^ n)) ⟩
  a * (a ^ n * b * b ^ n)
  ≡⟨ cong (a *_) (ass* (a ^ n) b (b ^ n)) ⟩
  a * (a ^ n * (b * b ^ n))
  ≡⟨ sym (ass* a (a ^ n) (b * b ^ n)) ⟩
  a * a ^ n * (b * b ^ n) ∎

sucinj : ∀{x y} → suc x ≡ suc y → x ≡ y
sucinj refl = refl