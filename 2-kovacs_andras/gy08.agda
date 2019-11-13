
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

-- implicit paraméterek: {}
ℕ-cong : (f : ℕ → ℕ) → {a b : ℕ} → ℕEq a b → ℕEq (f a) (f b)
ℕ-cong f eq = {!!}

-- ℕ-cong f {zero}  {zero}  eq = ℕ-refl (f zero)
-- ℕ-cong f {suc a} {suc b} eq = ℕ-cong (λ x → f (suc x)) eq

-- ℕ-subst (λ b → ℕEq (f a) (f b)) a b eq (ℕ-refl (f a))


-- ℕ tételek
------------------------------------------------------------

0+ : (a : ℕ) → ℕEq (0 + a) a
0+ a = {!!}

+0 : (a : ℕ) → ℕEq (a + 0) a
+0 a = {!!}

+suc : (a b : ℕ) → ℕEq (a + suc b) (suc (a + b))
+suc a b = {!!}

n-neq-sucn : (n : ℕ) → ¬ (ℕEq n (suc n))
n-neq-sucn n = {!!}

+-assoc : (a b c : ℕ) → ℕEq ((a + b) + c) (a + (b + c))
+-assoc a b c = {!!}

+-comm : (a b : ℕ) → ℕEq (a + b) (b + a)
+-comm a b = {!!}

0* : (a : ℕ) → ℕEq (0 * a) 0
0* a = {!!}

*0 : (a : ℕ) → ℕEq (a * 0) 0
*0 a = {!!}


-- Σ típus
------------------------------------------------------------

ex1 : Σ ℕ λ n → ℕEq n n
ex1 = 0 , ℕ-refl 0

ex2 : Σ ℕ λ n → ℕEq n n
ex2 = {!!}

ex3 : Σ ℕ λ n → ℕEq n n
ex3 = {!!}

ex4 : (n : ℕ) → Σ ℕ λ m → ℕEq n m
ex4 n = {!!}

ex5 : (n : ℕ) → Σ ℕ λ m → ¬ (ℕEq n m)
ex5 n = (suc n) , {!!}


pair : {A : Set}{B : A → Set}(a : A) → B a → Σ A B
pair = {!!}

proj₁' : {A : Set}{B : A → Set} → Σ A B → A
proj₁' ab = {!!}

proj₂' : {A : Set}{B : A → Set} → (ab : Σ A B) → B (proj₁' ab)
proj₂' ab = {!!}

-- típuselméleti "kiválasztási axióma"
choice : {A : Set}{B : A → Set}{C : (a : A) → B a → Set}
       → ((a : A) → Σ (B a) λ b → C a b)
       → Σ ((a : A) → B a) (λ f → (a : A) → C a (f a))
choice f = {!!}


-- vektorok, listák
------------------------------------------------------------

infix 5 _^_
_^_ : Set → ℕ → Set
A ^ n = {!!}

List : Set → Set
List A = {!!}

[] : {A : Set} → List A
[] = {!!}

infixr 4 _∷_
_∷_ : {A : Set} → A → List A → List A
_∷_ = {!!}
