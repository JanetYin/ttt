open import lib

{-
A = Bool
B true = ⊤
B false = ⊥

Σ A B = Σ Bool λ b → (if b then ⊤ else ⊥)

(a : A) → B a = (b : Bool) → if b then ⊤ else ⊥

(n : ℕ) → Vec ⊤ n  ≅  ℕ → ⊤  ≅  ⊤
                   =   1^n   =  1

Bool → ⊤   Bool → ⊥    (b:Bool) → if b then ⊤ else ⊥  ≅  ⊤ × ⊥
1^2        0^2 = 0*0   Π{i∈{0,1}}(f(i))               =  1 * 0
                          ahol f(0)=1
                               f(1)=0
                       Π(b∈Bool)(if b then 1 else 0)
      1
a*b = Π (f(i))   ahol f(0)=a és f(1)=b
      i=0
-}

-- √2 irrac
{-
√2 = a/b  2*b^2 = 2*(b'*2^m)^2 = 2^{2m+1} * (b'^2) ≠ 2^{2n} * a'^2 = (a'*2^n)^2 = a^2
-}
-- a,b irrac es a^b rac. klassz: (√2)^(√2), konstr: (√2)^(log_2(9)) =
--                                                  √(2^(log_2(9))) = √9 = 3
-- a:=b:=√2. LEM: ha (√2)^(√2) racionalis, akkor keszen vagyunk.
--                ha (√2)^(√2) irracionalis, akkor ((√2)^(√2))^(√2) = √2^((√2)*(√2)) =
--                                                 (√2)^2 = 2

-- De Morgan

-- ¬ (A ∧ B) ← ¬ A ∨ ¬ B
-- ((A × B) → ⊥) → ((A → ⊥) ⊎ (B → ⊥))

-- P : Bool → Type
-- (b : Bool) → P b  ↔   P true × P false
-- A = P i0 , B = P i1
firstOrderDeMorgan1 :
  (I : Type)(P : I → Type) →
   Σ I (λ i → ¬ P i) → ¬ ((i : I) → P i)
-- Σ Bool (λ i → ¬ (if i then A else B)) → ¬ ((i : I) → if i then A else B)
-- ¬ A ⊎ ¬ B                             → ¬ (A × B)
firstOrderDeMorgan1 I P (i , npi) f = npi (f i)

-- predicates, examples: Even, _≤_, _≡_mod_, _≟_
-- examples: (∀ x → P x ∧ Q x) ↔ (∀ x → P x) ∧ (∀ x → Q x), same with ∨, ∀ with ∃, both

-- summary table of logic

-- inductive Id type, sym, trans, cong, uncong(cannot pattern match), subst

Eq : ℕ → ℕ → Type
Eq zero zero = ⊤
Eq zero (suc _) = ⊥
Eq (suc _) zero = ⊥
Eq (suc m) (suc n) = Eq m n

data Vec (A : Type) : ℕ → Type where

data Id (A : Type)(a : A) : A → Type where
  refl : Id A a a

sym : {A : Type}(x y : A) → Id A x y → Id A y x
sym x .x refl = refl

trans : {A : Type}{x y z : A} → Id A x y → Id A y z → Id A x z
trans refl e' = e'

cong : {A B : Type}(f : A → B){x y : A} → Id A x y → Id B (f x) (f y)
cong f refl = refl

1≠2 : ¬ (Id ℕ 1 2)
1≠2 ()

uncong : ¬ ({A B : Type}(f : A → B){x y : A} → Id B (f x) (f y) → Id A x y)
uncong α = 1≠2 (α (λ _ → 0){1}{2} refl)

iteℕ : {A : Type} → A → (A → A) → ℕ → A
iteℕ z s zero = z
iteℕ z s (suc n) = s (iteℕ z s n)

-- iteId = subst

subst : {A : Type}(P : A → Type){x y : A} → Id A x y → P x → P y
subst P refl p = p

-- HF: megadni sym,trans,cong-ot subst segitsegevel

-- propositional vs definitional equality

-- osszeadas tulajdonsagai

-- a kovetkezo eloadas 2 perccel rovidebb
