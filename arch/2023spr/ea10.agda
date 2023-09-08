module ea10 where

open import lib

-- vizsgak: majdnem minden szeran 10-12 kozott MI laborban, gepteremben, peldavizsga

-- egyenloseg tipus: _≡_   teljes indukcio ℕ-on

indℕ : (P : ℕ → Set) → P zero → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
indℕ P pz ps zero = pz
indℕ P pz ps (suc n) = ps n (indℕ P pz ps n)

-- fuggo tipusu if-then-else-
-- iteBool :         Bool  → A      → A                    → A
indBool : (P : Bool → Set) → P true → P false → (b : Bool) → P b
indBool P pt pf true  = pt
indBool P pt pf false = pf

f : (b : Bool) → if b then Bool else ℕ
f b = indBool (λ b → if b then Bool else ℕ) true 3 b

-- strukturalis indukcio
{-
data T : Set where
  c1 : A{1,1} → ... → A{1,n_1}(t{1,1} ... t{1,k_1} : T) → T
  ...
  cm : A{m,1} → ... → A{m,n_m}(t{m,1} ... t{m,k_m} : T) → T

-- m db konstruktor

       v-motive     
indT : (P : T → Set)
       (pc1 : (a{1}:A{1,1})...(a{n_1}:A{1,n_1})(t1:T) → P t1 → ... → (t{k_1}:T) → P t{k_1} → P (c1 a{1} ... a{n_1} t1 ... t{k_1}))        -- 1. konstruktorhoz tartozo metodus
       ...
       (pcm : (a{1}:A{m,1})...(a{n_m}:A{m,n_m})(t1:T) → P t1 → ... → (t{k_m}:T) → P t{k_m} → P (cm a{1} ... a{n_1} t1 ... t{k_1})) →
       (t : T) → P t
indT P pc1 ... pcm (c1 a1 ... a{n_1} t1 ... t{k_1}) =
         pc1 a1 ... a{n_1} (indT ... t1) ... (indT ... t{k_1})
...

data List (A : Set) : Set where
  nil  : List A                -- n_1 = 0, k_1 = 0
  cons : A → List A → List A   -- n_2 = 1, k_2 = 1

data ℕ : Set where
  zero : ℕ        -- n_1 = 0, k_1 = 0
  suc  : ℕ → ℕ    -- n_2 = 0, k_2 = 1

-}

-- kommutativ monoid

record CommMonoid : Set₁ where
  field
    C    : Set
    _⊗_  : C → C → C
    u    : C
    ass  : (x y z : C) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    idl  : (x : C) → u ⊗ x ≡ x
    idr  : (x : C) → x ⊗ u ≡ x
    comm : (x y : C) → x ⊗ y ≡ y ⊗ x

cm1 : CommMonoid
cm1 = record
  { C = ⊤
  ; _⊗_ = λ _ _ → tt
  ; u = tt
  ; ass = λ _ _ _ → refl
  ; idl = λ _ → refl
  ; idr = λ _ → refl
  ; comm = λ _ _ → refl
  }

cm2-ass : (x y z : Bool) →
  (if if x then y else false then z else false) ≡
  (if x then if y then z else false else false)
cm2-ass false false z = refl
cm2-ass false true z = refl
cm2-ass true false z = refl
cm2-ass true true z = refl

_&&_ = λ x y → if x then y else false

cm2 : CommMonoid
cm2 = record
        { C = Bool
        ; _⊗_ = _&&_
        ; u = true
        ; ass = cm2-ass
        ; idl = λ _ → refl
        ; idr = indBool (λ x → (if x then true else false) ≡ x) refl refl 
        ; comm = λ { true true → refl ; true false → refl ; false true → refl ; false false → refl }
        }

open import ea08 
import ea09

comm-helper : (m n : ℕ) → suc (n + m) ≡ n + suc m
comm-helper m zero = refl
comm-helper m (suc n) = cong suc (comm-helper m n)

comm+ : (m n : ℕ) → m + n ≡ n + m
comm+ zero n = sym (ea09.idr n)
comm+ (suc m) n = trans (cong suc (comm+ m n)) (comm-helper m n)

cm3 : CommMonoid
cm3 = record
        { C = ℕ
        ; _⊗_ = _+_
        ; u = 0
        ; ass = ea09.assoc
        ; idl = ea09.idl
        ; idr = ea09.idr
        ; comm = comm+
        }

egyenlet : (cm : CommMonoid) → let open CommMonoid cm in
  (m n : C) → (m ⊗ m) ⊗ (n ⊗ u) ≡ m ⊗ (n ⊗ m)
egyenlet cm m n = trans
  (cong ((m ⊗ m) ⊗_) (idr n))
  (trans (ass m m n)
  (cong (m ⊗_) (comm m n)))
  where
    open CommMonoid cm

egyenletℕ : (m n : ℕ) → (m + m) + (n + 0) ≡ m + (n + m)
egyenletℕ = egyenlet cm3

egyenletBool : (m n : Bool) → (m && m) && (n && true) ≡ m && (n && m)
egyenletBool = egyenlet cm2

infix  3 _∎
infixr 2 _≡⟨_⟩_

_≡⟨_⟩_ : ∀{i}{A : Set i}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

_∎ : ∀{i}{A : Set i}(a : A) → a ≡ a
a ∎ = refl

egyenlet2 : (cm : CommMonoid) → let open CommMonoid cm in
  (x : C) → ((x ⊗ x) ⊗ (u ⊗ x)) ≡ (x ⊗ (u ⊗ (x ⊗ x)))
egyenlet2 cm x = let open CommMonoid cm in
  ((x ⊗ x) ⊗ (u ⊗ x))
                      ≡⟨ cong ((x ⊗ x) ⊗_) (comm u x) ⟩
  ((x ⊗ x) ⊗ (x ⊗ u))
                      ≡⟨ comm (x ⊗ x) ((x ⊗ u)) ⟩
  ((x ⊗ u) ⊗ (x ⊗ x))
                      ≡⟨ ass x u (x ⊗ x) ⟩
  (x ⊗ (u ⊗ (x ⊗ x)))
                      ∎

3≠2 : ¬ (3 ≡ 2)
3≠2 ()

nemnem12 : ¬ ((n : ℕ) → ¬ (n ≡ 1) → n ≡ 2)
nemnem12 h = 3≠2 (h 3 (λ { () }))

P : ℕ → Set
P 0 = ⊤
P 1 = ⊤
P 2 = ⊥
P 3 = ⊤
P _ = ⊤

3≠2' : ¬ (3 ≡ 2)
3≠2' e = subst P e tt

-- klassz vs konstr (√2)^(log_2(9)))
-- Kovetkezo előadás 13 perccel rövidebb.
