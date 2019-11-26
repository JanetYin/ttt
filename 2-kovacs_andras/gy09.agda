
open import lib

ℕEq : ℕ → ℕ → Set
ℕEq zero   zero     = ⊤
ℕEq zero   (suc m)  = ⊥
ℕEq (suc n) zero    = ⊥
ℕEq (suc n) (suc m) = ℕEq n m

ℕ-refl : (n : ℕ) → ℕEq n n
ℕ-refl zero    = tt
ℕ-refl (suc n) = ℕ-refl n

ℕ-sym : (n m : ℕ) → ℕEq n m → ℕEq m n
ℕ-sym zero zero eq = tt
ℕ-sym (suc n) (suc m) eq = ℕ-sym n m eq

ℕ-trans : (n m k : ℕ) → ℕEq n m → ℕEq m k → ℕEq n k
ℕ-trans zero zero zero eq1 eq2 = tt
ℕ-trans (suc n) (suc m) (suc k) eq1 eq2 =
  ℕ-trans n m k eq1 eq2

ℕ-subst : (P : ℕ → Set)(n m : ℕ) → ℕEq n m → P n → P m
ℕ-subst P zero zero eq pn = pn
ℕ-subst P (suc n) (suc m) eq pn =
  ℕ-subst (λ x → P (suc x)) n m eq pn

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero + b = b
suc a + b = suc (a + b)

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero  * b = zero
suc a * b = a * b + b


-- ℕ kongruencia
------------------------------------------------------------



-- implicit paraméterek
------------------------------------------------------------

-- Nem muszáj {a : _}-t sem definícióban,
-- sem függvényalkalmazásnál kiírni
id : {A : Set} → A → A
id x = x

foo : ℕ
foo = id 10

id' : {A : Set} → A → A
id' {A} x = x

foo' : ℕ
foo' = id {ℕ} 10

const : {A B : Set} → A → B → A
const x y = x

const' : {A : Set} → A → {B : Set} → B → A
const' x y = x

foo2 : ℕ
foo2 = const 10 10

foo3 : ℕ
foo3 = const {ℕ}{ℕ} 10 10

foo4 : ℕ
foo4 =
  case {_}{_}{_}{ℕ} {Bool} {ℕ} (inj₁ 0)
  (λ _ → 10) (λ _ → 20)


-- ℕ tételek
------------------------------------------------------------

ℕ-cong : (f : ℕ → ℕ) → (a b : ℕ) → ℕEq a b → ℕEq (f a) (f b)
ℕ-cong f zero    zero    eq = ℕ-refl (f zero)
ℕ-cong f (suc a) (suc b) eq = ℕ-cong (λ x → f (suc x)) a b eq

-- összeadás definíciójából triviális, hogy
-- 0 + a = a
0+ : (a : ℕ) → ℕEq (0 + a) a
0+ a = ℕ-refl a   -- C-u-C-c-C-,

-- definícióból nem következik azonnal, hogy
-- a + 0 = a
+0 : (a : ℕ) → ℕEq (a + 0) a
+0 zero = tt
  -- Goal : ℕEq (zero + 0) zero
  -- ℕEq és + definíció szerint ez ugyanaz, mint ⊤
+0 (suc a) = +0 a
  -- Goal : ℕEq (suc a + 0) (suc a)
  -- ℕEq és + definíció szerint ez ℕEq (a + 0) a

-- ℕ-refl + mintaillesztéssel a következő belátható:
+suc : (a b : ℕ) → ℕEq (a + suc b) (suc (a + b))
+suc zero b = ℕ-refl b
+suc (suc a) b = +suc a b

n-neq-sucn : (n : ℕ) → ¬ (ℕEq n (suc n))
n-neq-sucn zero p = p
n-neq-sucn (suc n) = n-neq-sucn n

+-assoc : (a b c : ℕ) → ℕEq ((a + b) + c) (a + (b + c))
+-assoc zero b c = ℕ-refl (b + c)
+-assoc (suc a) b c = +-assoc a b c

+-comm : (a b : ℕ) → ℕEq (a + b) (b + a)
+-comm zero    zero    = tt
+-comm zero    (suc b) = +-comm zero b
+-comm (suc a) zero    = +-comm a zero
+-comm (suc a) (suc b) =
  ℕ-trans (a + suc b) (suc (a + b)) (b + suc a)
          (ℕ-trans (a + suc b) (suc (b + a)) (suc (a + b))
                   (+-comm a (suc b))
                   (ℕ-sym (a + b) (b + a) (+-comm a b)))
          (+-comm (suc a) b)

   -- használni kell: ℕ-sym, ℕ-trans
   -- mi van, amit használni tudunk:
   --  1.  +-comm (suc a) b : ℕEq (suc (a + b)) (b + suc a)
   --  2.  +-comm a (suc b) : ℕEq (a + suc b) (suc (b + a))
   --  3.  +-comm a b       : ℕEq (a + b) (b + a)



-- Szimmetria, tranzitivitás, kongruencia
------------------------------------------------------------

g1 : ∀ x y z → ℕEq x y → ℕEq y z → ℕEq z x
g1 x y z p q =
  let eq : ℕEq x z
      eq = ℕ-trans x y z p q
  in ℕ-sym x z eq

-- ∀ : rövidített jelölés függvényre
-- (x y : ℕ) → ..
g2 : ∀ x y → ℕEq x y → ℕEq (suc (suc x)) (suc (suc y))
g2 x y eq = ℕ-cong (λ x → suc (suc x)) x y eq

g3 : ∀ (f : ℕ → ℕ) x y  → ℕEq x y → ℕEq (f y) (f x)
g3 f x y eq =
    ℕ-sym (f x) (f y) (ℕ-cong f x y eq)
    -- másik: ℕ-cong f y x (ℕ-sym x y eq)

g4 : ∀ x y z → ℕEq (suc x) z → ℕEq (suc y) z → ℕEq y x
g4 x y z eq1 eq2 =
   let eq2' = ℕ-sym (suc y) z eq2
       macska = ℕ-trans (suc x) z (suc y) eq1 eq2'
   in ℕ-sym x y macska


-- Σ típus
------------------------------------------------------------

-- _×_

ex1 : Σ ℕ (λ n → ℕEq n n)
ex1 = 10 , tt

-- minden n : ℕ -re megad egy m : ℕ-t
-- amire igaz, hogy ℕEq n m
-- "létezik"
ex4 : (n : ℕ) → Σ ℕ (λ m → ℕEq n m)
ex4 n = n , ℕ-refl n

ex5 : (n : ℕ) → Σ ℕ λ m → ¬ (ℕEq n m)
ex5 n = (suc n) , (n-neq-sucn n)

pair : {A : Set}{B : A → Set}(a : A) → B a → Σ A B
pair a b = a , b

proj₁' : {A : Set}{B : A → Set} → Σ A B → A
proj₁' ab = proj₁ ab

proj₂' : {A : Set}{B : A → Set}
       → (ab : Σ A B) → B (proj₁' ab)
proj₂' ab = proj₂ ab

-- (ha minden a : A-ra igaz P a és Q a)
-- ekvivalens azzal, hogy
-- ((minden a : A-ra igaz P a) ÉS (minden a : A-ra igaz Q a)

-- ez annak az általánosítása, hogy:
--   (A → B × C) ↔ ((A → B) × (A → C))

f1 : (A : Set)(P : A → Set)(Q : A → Set)
   → ((a : A) → P a × Q a)
   ↔ (((a : A) → P a) × ((a : A) → Q a))
f1 A P Q =
    (λ f → (λ a → proj₁ (f a)) , (λ a → proj₂ (f a)))
  , (λ fg → λ a → (proj₁ fg a) , (proj₂ fg a))

-- nulladrendű (nem függő) speciális eset
-- (A → P ⊎ Q) ← ((A → P) ⊎ (A → Q))

f2 : (A : Set)(P : A → Set)(Q : A → Set)
     → ((a : A) → P a ⊎ Q a)
     ← ((a : A) → P a) ⊎ ((a : A) → Q a)
f2 A P Q (inj₁ f) a = inj₁ (f a)
f2 A P Q (inj₂ g) a = inj₂ (g a)

-- nem függő: A × (B × C) → (A × B) × (A × C)
f3 : (A : Set)(P : A → Set)(Q : A → Set)
    → (Σ A λ a → P a × Q a)
    → Σ A P × Σ A Q
f3 = {!!}

f4 : (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a)  ↔ Σ A P ⊎ Σ A Q
f4 = {!!}

f5 : (A : Set)(P : A → Set) → (Σ A λ a → ¬ P a) → ¬ ((a : A) → P a)
f5 = {!!}

f6 : (A : Set)(P : A → Set) → (¬ Σ A λ a → P a) ↔ ((a : A) → ¬ P a)
f6 = {!!}

f7 : (A B : Set) → (A ⊎ B) ↔ Σ Bool (λ b → if b then A else B)
f7 = {!!}

-- típuselméleti "kiválasztási axióma"
choice : {A : Set}{B : A → Set}{C : (a : A) → B a → Set}
       → ((a : A) → Σ (B a) λ b → C a b)
       → Σ ((a : A) → B a) (λ f → (a : A) → C a (f a))
choice f = {!!}


-- vektorok
------------------------------------------------------------

infix 5 _^_
_^_ : Set → ℕ → Set
A ^ n = {!!}
