module gy9 where

open import lib

⊎×dist : (A B C : Set) → (A ⊎ B) × C ↔ (A × C) ⊎ (B × C)
⊎×dist = {!!}

×⊎dist : (A B C : Set) → (A × B) ⊎ C ↔ (A ⊎ C) × (B ⊎ C) -- this is not an isomorphism
×⊎dist = {!!}

squared : (A : Set) → (Bool → A) ↔ A × A
squared = {!!}

test1 : ℕ × ℕ
test1 = proj₁ (squared ℕ) (proj₂ (squared ℕ) (3 , 2))

test2 : Bool → ℕ
test2 = proj₂ (squared ℕ) (proj₁ (squared ℕ) (λ b → if b then 3 else 2))

transitivity : (A B C : Set) → (A ↔ B) → (B ↔ C) → (A ↔ C)
transitivity = {!!}

lemma : (A B : Set) → (A ↔ B) → ((Bool → A) ↔ (Bool → B))
lemma = {!!}

lem0' : (A B : Set) → (A → (B × B)) ↔ (A → Bool → B)
lem0' = {!!}

lemma2 : (A : Set) → (Bool → A ⊎ ⊤) ↔ ((Bool → A) ⊎ (Bool × A) ⊎ ⊤)
lemma2 = {!!}

+² : (A B : Set) → (Bool → (A ⊎ B)) ↔ ((Bool → A) ⊎ (Bool × A × B) ⊎ (Bool → B))
+² = {!!}

Eqb : Bool → Bool → Set
Eqb = {!!}

not : Bool → Bool
not = {!!}

ex : Σ Bool (λ b → Eqb (not b) false)
ex = {!!}

-- sigma:
-- record Σ {i}{j}(A : Set i)(B : A → Set j) : Set (i ⊔ j) where
--   constructor _,_
--   field
--     proj₁ : A
--     proj₂ : B proj₁
currying : (A C : Set) → (P : A → Set) → (Σ A P → C) ↔ ((x : A) → (P x → C))
currying = {!!}

-- (Σ A P → C) ↔ ((x : A) → (P x → C))
-- indBool : ∀{i}(P : Bool → Set i) → P true → P false → (t : Bool) → P t
-- indBool P u v true = u
-- indBool P u v false = v
ex2 : (A B : Set) → Σ Bool (λ b → if b then A else B) ↔ (A ⊎ B) 
ex2 = {!!}

--

true=true : Eqb true true
true=true = {!!}

¬true=false : ¬ Eqb true false
¬true=false = {!!}

lem1 : (x : Bool) → Eqb true x → ¬ Eqb x false
lem1 = {!!}

Eqb-refl : (x : Bool) → Eqb x x
Eqb-refl = {!!}

ID : (A : Set) → A → A
ID = {!!}

CONST : (A B : Set) → A → B → A
CONST = {!!}

comm× : (A B : Set) → (A × B) ↔ (B × A)
comm× = {!!}

comm⊎ : (A B : Set) → (A ⊎ B) ↔ (B ⊎ A)
comm⊎ = {!!}

module firstOrder
  (A B : Set)
  (P Q : A → Set)
  (R : A → B → Set)
  where

  ∀×-distr : ((x : A) → P x × Q x) ↔ ((x : A) → P x) × ((x : A) → Q x)
  ∀×-distr = {!!}

  ∀⊎-distr : ((x : A) → P x ⊎ Q x) ← ((x : A) → P x) ⊎ ((x : A) → Q x)
  ∀⊎-distr = {!!}
  
  Σ×-distr : (Σ A λ x → P x × Q x) → Σ A P × Σ A Q
  Σ×-distr = {!!}

  Σ⊎-distr : (Σ A λ x → P x ⊎ Q x) ↔ Σ A P ⊎ Σ A Q
  Σ⊎-distr = {!!}

  ¬¬∀-nat : ¬ ¬ ((x : A) → P x) → (x : A) → ¬ ¬ (P x)
  ¬¬∀-nat = {!!}

  Σ∀ : (Σ A λ x → (y : B) → R x y) → ∀(y : B) → Σ A λ x → R x y
  Σ∀ = {!!}

  AC : (∀(x : A) → Σ B λ y → R x y) → Σ (A → B) λ f → ∀(x : A) → R x (f x)
  AC = {!!}

  -- first order De Morgan

  ¬∀ : (Σ A λ x → ¬ P x) → ¬ ((x : A) → P x)
  ¬∀ = {!!}

  ¬Σ : (¬ Σ A λ x → P x) ↔ ((x : A) → ¬ P x)
  ¬Σ = {!!}


infixl 4 _+_
_+_ : ℕ → ℕ → ℕ
_+_ = λ x y → primrec y (λ _ z → suc z) x
eq : ℕ → ℕ → Bool
eq = λ x → primrec
                 (λ y → primrec true (λ _ _ → false) y)
                 (λ x' eq? y → primrec false (λ y' _ → eq? y') y)
                 x
Eqn : ℕ → ℕ → Set
Eqn = λ x y → Eqb (eq x y) true

refl-= : (n : ℕ) → Eqn n n
refl-= = {!!}

0lid : (n : ℕ) → Eqn (zero + n) n 
0lid = {!!}

0rid : (n : ℕ) → Eqn (n + zero) n 
0rid = {!!}

0rid' : (n : ℕ) → Eqn n (n + zero) 
0rid' = {!!}

lem : (a b : ℕ) → Eqn (suc (a + b)) (a + suc b)
lem = {!!}

comm+ : (a b : ℕ) → Eqn (a + b) (b + a)
comm+ = {!!}

-- 1 + a + 2 * 0 = a + 1
exercise1 : (A : Set) → ⊤ ⊎ A ⊎ Bool × ⊥ ↔ A ⊎ ⊤
exercise1 = {!!}
