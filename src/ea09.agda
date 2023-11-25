open import Lib hiding (_≡_; refl)

-- head : List A → Maybe A

-- allitas        -> tipus
-- bizonyitas     -> term
-- ha A, akkor B  -> A → B
-- A iff B        -> A ↔ B
-- A és B         -> A × B
-- A vagy B       -> A ⊎ B
-- nem A          -> A → ⊥
-- ∀(x:ℕ).P(x)    -> (x : ℕ) → P x
-- ∃(x:ℕ).P(x)    -> Σ ℕ P

infix 4 _≡_
data _≡_ {A : Set} : A → A → Set where
  refl : (n : A) → n ≡ n

1+2+3=6 : 1 + 2 + 3 ≡ 6
1+2+3=6 = refl 6

1+ : (n : ℕ) → 1 + n ≡ suc n
1+ n = refl (suc n)

postulate +-comm : (a b : ℕ) → a + b ≡ b + a -- jovo oran

+1 : (n : ℕ) → n + 1 ≡ suc n
+1 n = +-comm n 1

_≤_ : ℕ → ℕ → Set
m ≤ n = Σ ℕ λ k → k + m ≡ n   -- alternativ definicio

3≤12 : 3 ≤ 12
3≤12 = 9 , refl 12

-- HF: bizonyitsd be, hogy a mult orai _≤_-vel ekvivalens

record _≅_ (A B : Set) : Set where
  field
    from : A → B
    to   : B → A
    fromto : (y : B) → from (to y) ≡ y
    tofrom : (x : A) → to (from x) ≡ x

-- ∀(x:A).(P(x)∧Q(x)) ↔ ∀x.P(x)∧∀x.Q(x)   -- A → (P × Q)  ↔  (A → P) × (A → Q)
module _ (A : Set)(P Q : A → Set) where
  to : ((x : A) → P x × Q x) → ((x : A) → P x) × ((x : A) → Q x)
  to f = (λ x → fst (f x)) , (λ x → snd (f x))
  from : ((x : A) → P x) × ((x : A) → Q x) → (x : A) → P x × Q x
  from (f , g) x = f x , g x
  fromto : (f : (x : A) → P x × Q x) → from (to f) ≡ f
  fromto f = refl _  -- f =(→η) (λ x → f x) =(×η) (λ x → (fst (f x) , snd (f x)))
  tofrom : (fg : ((x : A) → P x) × ((x : A) → Q x)) → to (from fg) ≡ fg
  tofrom _ = refl _

  iso : ((x : A) → P x × Q x) ≅ (((x : A) → P x) × ((x : A) → Q x))
  _≅_.from   iso = to
  _≅_.to     iso = from
  _≅_.fromto iso = tofrom
  _≅_.tofrom iso = fromto

-- to : (A : Set)(P Q : A → Set)((x : A) → ...) → ...

-- ∀(P∨Q) ← ∀P∨∀Q

isEven isOdd : ℕ → Set
isEven zero = ⊤                    -- isEven zero = ⊤
isEven (suc zero) = ⊥              -- isEven (suc n) = ¬ (isEven n)
isEven (suc (suc n)) = isEven n

isOdd n = ¬ (isEven n)

nemMindenParos : ¬ (∀ n → isEven n)  -- ELSO AGDABELI NEGACIO BIZONYITASOM
nemMindenParos f = f 1

nemMindenParatlan : ¬ (∀ n → isOdd n)
nemMindenParatlan f = f 0 tt  -- isOdd 0 = ¬ (isEven zero) = ¬ ⊤ = ⊤ → ⊥

minden*os : (n : ℕ) → isEven n ⊎ isOdd n      -- teljes indukcio
minden*os zero = inl tt
minden*os (suc zero) = inr (λ x → x)
minden*os (suc (suc n)) = minden*os n
-- isEven (suc (suc n)) ⊎ isOdd (suc (suc n)) =
-- isEven n ⊎ ¬ isEven (suc (suc n)) =
-- isEven n ⊎ ¬ isEven n =
-- isEven n ⊎ isOdd n

seged : {A B : Set} → A ⊎ B → ¬ A → ¬ B → ⊥
seged (inl a) na nb = na a
seged (inr b) na nb = nb b

nem∀+ : ¬ ((A : Set)(P Q : A → Set) → ((x : A) → P x ⊎ Q x) →
           (∀ x → P x) ⊎ (∀ x → Q x))
nem∀+ f = seged (f ℕ isEven isOdd minden*os) nemMindenParos nemMindenParatlan 

-- (1) ∃x.(P(x)∧Q(x)) ↔ (∃x.P(x))∧(∃x.Q(x))    EGYIK IRANY NEM JO
-- HF: bebizonyitani, hogy az egyik irany jo, a masik nem

-- (2) ∃x.(P(x)∨Q(x)) ↔ (∃x.P(x))∨(∃x.Q(x))    4
-- HF: bebizonyitani, hogy jo

-- megnezendo video:
-- https://www.youtube.com/watch?v=ebMY3VH_K1U

-- jovo oran:

-- ≡, sym,trans, cong, subst, prop/def, pl.: bool fgv-ek

-- indukcio
