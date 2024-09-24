-- BEGIN FIX
{-# OPTIONS --guardedness --safe #-}

open import Lib.Level
open import Lib.Function
open import Lib.Nat
  renaming (_≟_ to _≟ℕ_)
open import Lib.Empty
  renaming (_≟_ to _≟⊥_)
open import Lib.Unit
  renaming (_≟_ to _≟⊤_)
open import Lib.Equality
open import Lib.Sum
  renaming (map to map⊎)
open import Lib.Sigma
  renaming (map to mapΣ)
open import Lib.Containers.Stream.Type
open import Lib.Containers.Vector.Type
open import Lib.Fin
open import Lib.Bool
  renaming ( contradiction to contradictionᵇ
           ; contraposition to contrapositionᵇ
           ; _≟_ to _≟ᵇ_)
open import Lib.Dec
open import Lib.Conat.Type
open import Lib.Conat.Base
  renaming (_+_ to _+∞_ ; _+'_ to _+∞'_ ; _*_ to _*∞_ ; _^_ to _^∞_)
open import Lib.Conat.Literals
open import Lib.Maybe
open import Lib.Class.Eq
open import Lib.Class.Ord
import Lib.Containers.Stream as S
import Lib.Containers.Vector as V

_≤_ : ℕ → ℕ → Set
n ≤ k = Σ ℕ λ m → m + n ≡ k
infix 5 _≤_
-- END FIX

-- BEGIN FIX
-- HU: b1 és b2 legyen úgy definiálva, hogy b1 ℕ 1 2 ≠ b2 ℕ 1 2
-- EN: b1 and b2 should be such that b1 ℕ 1 2 ≠ b2 ℕ 1 2
b1 b2 : (A : Set) → A → A → A
-- END FIX
b1 A x x₁ = x
b2 A x x₁ = x₁
-- BEGIN FIX
test-b1-b2 : ¬ (b1 ℕ 1 2 ≡ b2 ℕ 1 2)
test-b1-b2 ()
-- END FIX

-- -- BEGIN FIX
-- -- HU: Segítség: mire hasonlít a függvény típusa, ha balról jobbra olvassuk?
-- -- EN: Hint: What does the function's type resemble to when reading the type from left to right?
-- boolIso : Bool ↔ ((A : Set) → A → A → A)
-- -- END FIX
-- fst boolIso false A t f = f
-- fst boolIso true A t f = t
-- snd boolIso x with x Bool true false 
-- ... | false = false
-- ... | true = true
-- -- BEGIN FIX
-- test-boolIso-1 : snd boolIso (fst boolIso false) ≡ false
-- test-boolIso-1 = refl
-- test-boolIso-2 : snd boolIso (fst boolIso true) ≡ true
-- test-boolIso-2 = refl
-- test-boolIso-3 : fst boolIso (snd boolIso (λ _ x _ → x)) ≡ (λ _ x _ → x)
-- test-boolIso-3 = refl
-- test-boolIso-4 : fst boolIso (snd boolIso (λ _ _ x → x)) ≡ (λ _ _ x → x)
-- test-boolIso-4 = refl
-- -- END FIX

-- -- BEGIN FIX
-- assΣ1 : ∀{A : Set}{B : A → Set}{C : (a : A) → B a → Set} →
--     Σ A (λ a → Σ (B a) λ b → C a b) ↔ Σ (Σ A B) λ ab → C (fst ab) (snd ab)
-- -- END FIX
-- fst assΣ1 x = ((fst x) , (fst (snd x))) , (snd (snd x))
-- snd assΣ1 x = fst (fst x) , (snd (fst x)) , snd x

-- -- BEGIN FIX
-- --A × B (B → A ⊎ ¬ B)  → ¬A --impossible
-- ¬ab : ¬ ((A B : Set) → A × B → (A ⊎ ¬ B ↔ B) → ¬ A)
-- ¬ab x with x A B p1 (p4 , p3) true
--   where 
--     A B : Set 
--     A = Bool
--     B = Bool
--     p1 : A × B
--     p1 = true , true
--     p3 : B → A ⊎ ¬ B
--     p3 x = inl true
--     p4 : A ⊎ ¬ B → B 
--     p4 x = case x (λ x₂ → true) (λ x₂ → false)
-- ... | () 
-- ¬ab2 : ¬ ((A B : Set) → (A × B) → (((A ⊎ ¬ B) ↔ B) ↔ ¬ A))
-- ¬ab2 x = fst (x A B p1) (p4 , p3) true
--     where 
--       A B : Set 
--       A = Bool
--       B = Bool
--       p1 : A × B
--       p1 = true , true
--       p3 : B → A ⊎ ¬ B
--       p3 x = inl true
--       p4 : A ⊎ ¬ B → B 
--       p4 x = case x (λ x₂ → true) (λ x₂ → false)

-- ab : ((A B : Set) → (A × B) → (((A ⊎ ¬ B) ↔ B) ↔ ¬ A)) ⊎ ¬ ((A B : Set) → (A × B) → (((A ⊎ ¬ B) ↔ B) ↔ ¬ A))
-- -- END FIX
-- ab = inr λ x → ¬ab2 x 

-- -- BEGIN FIX
-- tr : (a b : ℕ) → ((P : ℕ → Set) → P a → P b) → a ≡ b
-- -- END FIX
-- tr a b  = λ x → x P refl 
--   where 
--     P : ℕ → Set 
--     P b = a ≡ b

-- -- BEGIN FIX
-- fgcomm : (x y : ℕ) → (f g : ℕ → ℕ) → f x + g y ≡ g y + f x
-- -- END FIX
-- fgcomm x y f g = comm+ (f x) (g y) 

-- -- BEGIN FIX
-- lemma8 : ¬ ((a b : ℕ) → a ≡ b)
-- -- END FIX
-- lemma8 x with x 1 2 
-- ... | ()

-- injsuc : {n k : ℕ} → suc n ≡ suc k → n ≡ k
-- injsuc refl = refl
-- -- n + (x + y) ≡ x + y + n ≡ x + z
-- -- +n : (x y z n : ℕ) → → x + n ≡ y + n  
-- n+ : (x y z n : ℕ)  → n + (x + y) ≡ x + (n + y)
-- n+ x y z n = trans (comm+ n (x + y)) (trans (assoc+ x y n) (cong (λ a → x + a) (comm+ y n))) 

-- p21 : (x y z n : ℕ) →  n + (x + y) ≡ x + z → x + (n + y) ≡ x + z 
-- p21 x y z n x₁ = trans  (n+ n y z x) x₁
 
-- p2 : (x y z n : ℕ) → x + (y + n) ≡ x + z → y + n ≡ z
-- p2 zero y z n x₁ = x₁
-- p2 (suc x) y z n x₁ = p2 x y z n (injsuc x₁) 

-- x+≤inj : (x y z : ℕ) → x + y ≤ x + z → y ≤ z
-- -- END FIX
-- x+≤inj x y z (n , n→z) = n , (p2 x n z  y) ((p21 x y z n)  n→z) 

-- +-suc : ∀ n → n + 1 ≡ suc n
-- +-suc zero    = refl
-- +-suc (suc n) = cong suc (+-suc n)

-- -- BEGIN FIX
-- x+1 : (λ x → x + 1) ≢ (λ y → y)
-- -- END FIX
-- x+1 x  = proof x
--   where
--     1≡0 : 1 ≡ zero → ⊥ 
--     irrelevant (1≡0 ())
--     proof : (λ x → x + 1) ≡ (λ y → y) → ⊥
--     proof eq = 1≡0 (cong (λ f → f zero) eq)  
    
-- -- BEGIN FIX
-- fincomm : (n k : ℕ) → Fin (n + k) → Fin (k + n)
-- -- END FIX
-- fincomm n k x = subst (Fin) (comm+ n k) x
-- -- BEGIN FIX
-- test-fincomm-1 : fincomm 0 1 0 ≡ 0
-- test-fincomm-1 = refl
-- test-fincomm-2 : fincomm 1 0 0 ≡ 0
-- test-fincomm-2 = refl
-- test-fincomm-3 : fincomm 4 6 0 ≡ 0
-- test-fincomm-3 = refl
-- test-fincomm-4 : fincomm 4 6 1 ≡ 1
-- test-fincomm-4 = refl
-- test-fincomm-5 : fincomm 4 6 2 ≡ 2
-- test-fincomm-5 = refl
-- test-fincomm-6 : fincomm 4 6 3 ≡ 3
-- test-fincomm-6 = refl
-- test-fincomm-7 : fincomm 4 6 4 ≡ 4
-- test-fincomm-7 = refl
-- test-fincomm-8 : fincomm 4 6 5 ≡ 5
-- test-fincomm-8 = refl
-- test-fincomm-9 : fincomm 4 6 6 ≡ 6
-- test-fincomm-9 = refl
-- test-fincomm-10 : fincomm 4 6 7 ≡ 7
-- test-fincomm-10 = refl
-- test-fincomm-11 : fincomm 4 6 8 ≡ 8
-- test-fincomm-11 = refl
-- test-fincomm-12 : fincomm 4 6 9 ≡ 9
-- test-fincomm-12 = refl
-- -- END FIX
  
  
boolIso : Bool ↔ ((A : Set) → A → A → A)
-- END FIX
boolIso = {!   !}
-- BEGIN FIX
test-boolIso-1 : snd boolIso (fst boolIso false) ≡ false
test-boolIso-1 = refl
test-boolIso-2 : snd boolIso (fst boolIso true) ≡ true
test-boolIso-2 = refl
test-boolIso-3 : fst boolIso (snd boolIso (λ _ x _ → x)) ≡ (λ _ x _ → x)
test-boolIso-3 = refl
test-boolIso-4 : fst boolIso (snd boolIso (λ _ _ x → x)) ≡ (λ _ _ x → x)
test-boolIso-4 = refl
-- END FIX
injsuc : {n k : ℕ} → suc n ≡ suc k → n ≡ k
injsuc = {!   !}
-- BEGIN FIX
assΣ1 : ∀{A : Set}{B : A → Set}{C : (a : A) → B a → Set} →
    Σ A (λ a → Σ (B a) λ b → C a b) ↔ Σ (Σ A B) λ ab → C (fst ab) (snd ab)
-- END FIX
fst assΣ1 x = ((fst x) , (fst (snd x))) , (snd (snd x))
snd assΣ1 x = (fst (fst x)) , (snd (fst x)) , snd x


-- BEGIN FIX
-- A × B (B → A ⊎ ¬ B)  → ¬A --impossible
-- ¬ab : ¬ ((A B : Set) → A × B → (A ⊎ ¬ B ↔ B) → ¬ A)
-- ¬ab x = ?
¬ab2 : ¬ ((A B : Set) → (A × B) → (((A ⊎ ¬ B) ↔ B) ↔ ¬ A))
¬ab2 x = fst (x ⊤ ⊤ (tt , tt)) ((λ x₁ → tt) , λ x₁ → inl tt) tt

ab : ((A B : Set) → (A × B) → (((A ⊎ ¬ B) ↔ B) ↔ ¬ A)) ⊎ ¬ ((A B : Set) → (A × B) → (((A ⊎ ¬ B) ↔ B) ↔ ¬ A))
-- END FIX
ab = inr ¬ab2
  
-- BEGIN FIX
tr : (a b : ℕ) → ((P : ℕ → Set) → P a → P b) → a ≡ b
-- END FIX
tr a b x = x P refl
  where 
    P : ℕ → Set 
    P x =  a ≡ x 

-- BEGIN FIX
fgcomm : (x y : ℕ) → (f g : ℕ → ℕ) → f x + g y ≡ g y + f x
-- END FIX
fgcomm = {!   !}

-- BEGIN FIX
lemma8 : ¬ ((a b : ℕ) → a ≡ b)
-- END FIX
lemma8 = {!   !}


-- n + (x + y) ≡ x + y + n ≡ x + z
-- +n : (x y z n : ℕ) → → x + n ≡ y + n  
n+ : (x y z n : ℕ)  → n + (x + y) ≡ x + (n + y)
n+ = {!   !}
   
-- p21 : (x y z n : ℕ) →  n + (x + y) ≡ x + z → x + (n + y) ≡ x + z 
-- p21 x y z n x₁ = trans  (n+ n y z x) x₁
 
-- p2 : (x y z n : ℕ) → x + (y + n) ≡ x + z → y + n ≡ z
-- p2 = ?
x+≤inj : (x y z : ℕ) → x + y ≤ x + z → y ≤ z
-- END FIX
x+≤inj x y z (n , snd₁) = n , trans (comm+ n y) (p2 {x} {y} {n} (p1 ))
  where 
    p1 :   x + (y + n) ≡ x + z
    p1 = (trans ( sym (assoc+ x y n)) (trans (comm+ (x + y) n ) snd₁))
    p2 :  ∀ {x y n} → x + (y + n) ≡ x + z → y + n ≡ z 
    p2 {zero} {y} {n} x₁ = x₁
    p2 {suc x} {y} {n} x₁ = p2 {x} {y} {n}  (injsuc x₁)

+-suc : ∀ n → n + 1 ≡ suc n
+-suc zero = refl
+-suc (suc n) = (cong suc (+-suc n))
  where
    suc-inj : ∀ {n k} → suc n ≡ suc k → n ≡ k 
    suc-inj refl = refl

-- BEGIN FIX
x+1 : ((λ x → x + 1) ≡ (λ y → y)) → ⊥
-- END FIX
x+1 x = 1≡\0 (cong (λ f → f zero) x)
  where 
    1≡\0 : 1 ≡ zero → ⊥
    1≡\0 ()

    
-- BEGIN FIX
fincomm : (n k : ℕ) → Fin (n + k) → Fin (k + n)
-- END FIX
fincomm n k x = subst Fin (comm+ n k) x
-- BEGIN FIX
test-fincomm-1 : fincomm 0 1 0 ≡ 0
test-fincomm-1 = refl
test-fincomm-2 : fincomm 1 0 0 ≡ 0
test-fincomm-2 = refl
test-fincomm-3 : fincomm 4 6 0 ≡ 0
test-fincomm-3 = refl
test-fincomm-4 : fincomm 4 6 1 ≡ 1
test-fincomm-4 = refl
test-fincomm-5 : fincomm 4 6 2 ≡ 2
test-fincomm-5 = refl
test-fincomm-6 : fincomm 4 6 3 ≡ 3
test-fincomm-6 = refl
test-fincomm-7 : fincomm 4 6 4 ≡ 4
test-fincomm-7 = refl
test-fincomm-8 : fincomm 4 6 5 ≡ 5
test-fincomm-8 = refl
test-fincomm-9 : fincomm 4 6 6 ≡ 6
test-fincomm-9 = refl
test-fincomm-10 : fincomm 4 6 7 ≡ 7
test-fincomm-10 = refl
test-fincomm-11 : fincomm 4 6 8 ≡ 8
test-fincomm-11 = refl
test-fincomm-12 : fincomm 4 6 9 ≡ 9
test-fincomm-12 = refl
-- END FIX  