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
-- HU: Kisebb-e a szám, mint 1000?
-- EN: Is the number smaller than 1000?
-- is<1000 : ℕ → Bool
-- -- END FIX
-- is<1000 n = n < 1000
-- -- BEGIN FIX
-- test-is<1000-1 : is<1000 1000 ≡ false
-- test-is<1000-1 = refl
-- test-is<1000-2 : is<1000 999 ≡ true
-- test-is<1000-2 = refl
-- test-is<1000-3 : is<1000 1001 ≡ false
-- test-is<1000-3 = refl
-- test-is<1000-4 : is<1000 0 ≡ true
-- test-is<1000-4 = refl
-- -- END FIX

-- -- BEGIN FIX
-- iso'' : (X Y Z : Set) → (X → (Z × Y)) ↔ ((X → Y ⊎ ⊥) × (X ⊎ ⊥ → Z))
-- -- END FIX
-- iso'' X Y Z = (λ x → (λ x₁ → inl (snd (x x₁))) , (λ {(inl a) → fst (x a)})) , 
--               λ {(toy , toz) x₁ → toz (inl x₁) , case (toy x₁) (λ x → x) (λ x → exfalso x)}

-- -- BEGIN FIX
-- fff : (A B : Set) → (A ⊎ B) ↔ Σ Bool (λ b → if b then A else B)
-- -- END FIX
-- fst (fff A B) (inl a) = true , a
-- fst (fff A B) (inr b) = false , b
-- snd (fff A B) (false , b) = inr b
-- snd (fff A B) (true , a) = inl a

-- -- BEGIN FIX
-- notexist : ¬ ((P Q : Set) → ¬ P ⊎ Q ↔ P → P × ¬ Q )
-- notexist x with x P Q prod
--   where
--     P : Set
--     P = ⊤
--     Q : Set
--     Q = ⊤
--     prod : ¬ P ⊎ Q ↔ P 
--     fst prod x = tt
--     snd prod x = inr tt
-- ... | fst₁ , snd₁ = snd₁ tt

-- ¬pq : ((P Q : Set) → (¬ P ⊎ Q) ↔ P → P × ¬ Q) ⊎ ¬ ((P Q : Set) → (¬ P ⊎ Q) ↔ P → P × ¬ Q)
-- -- END FIX
-- ¬pq = inr notexist

-- -- BEGIN FIX

-- weee₂ : (n k : ℕ) → ((P : ℕ → Set) → P n → P k) ↔ n ≡ k
-- -- END FIX
-- weee₂ n k = (λ x → x P refl)  , (λ {refl P Pn → Pn})
--   where 
--     P : ℕ → Set
--     P m = n ≡ m
-- weee₂ : (n k : ℕ) → ((P : ℕ → Set) → P n → P k) ↔ n ≡ k
-- -- END FIX
-- fst (weee₂ n k) x = x {!   !} {!   !}
-- snd (weee₂ n .n) refl P' x₁ = x₁
--   where 
--     P : ℕ → Set
--     P x = x ≡ n

-- -- BEGIN FIX
-- trans≤ : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
-- -- END FIX
-- trans≤ x .(a + x) .(b + (a + x)) (a , refl) (b , refl) = (a + b) , sym (trans (comm+ b (a + x)) (trans (assoc+ a x b) (sym (trans (assoc+ a b x) (sym (cong (λ y → a + y )  (comm+ x b))))))) 

-- p1^ : (n : ℕ) → 1 ^ n ≡ 1
-- p1^ zero = refl
-- p1^ (suc n) = trans (idr+ (1 ^ n)) (p1^ n)

-- -- BEGIN FIX
-- suc^ : (n m : ℕ) → Σ ℕ λ k → suc n ^ m ≡ suc k
-- -- END FIX
-- suc^ zero m = zero , (p1^ m)
-- suc^ (suc n) zero = zero , refl
-- suc^ (suc n) (suc m) with suc^ (suc n) m
-- ... | (k , p) =  (k + suc (k + n * suc k)) , p1 
--   where
--     p1 : suc (suc n) ^ m + (suc (suc n) ^ m + n * suc (suc n) ^ m) ≡ suc (k + suc (k + n * suc k))
--     p1 = 
--        suc (suc n) ^ m + (suc (suc n) ^ m + n * suc (suc n) ^ m)
--         ≡⟨ cong (λ x → x + ( x +  n * x)) p ⟩
--         suc (k + suc (k + n * suc k)) 
--         ∎
        
-- -- BEGIN FIX
-- pred2 : Σ ℕ (λ m → m + 3 ≡ 4) ⊎ Σ ℕ (λ m → m + 5 ≡ 2) ⊎ Σ ℕ (λ m → m + 6 ≡ 1)
-- pred2 = inl ((suc zero) , refl)

-- ineq : ¬ ((a b c : ℕ) → a + b ≤ c ⊎ c + b ≤ a ⊎ a + c ≤ b → c ≤ b ⊎ a ≤ b) -- b is the longest
-- -- END FIX
-- ineq x with x 2 1 4
-- ... | u with u pred2 
-- ... | inl (suc zero , ())
-- ... | inl (suc (suc fst₁) , ())
-- ... | inr (suc zero , ())
-- ... | inr (suc (suc fst₁) , ())

-- -- BEGIN FIX
-- ffg : ¬ ((R : ℕ × ℕ → Set) → (Σ (ℕ × ℕ) R) → Σ ℕ (λ x → R (x , x)))
-- -- END FIX
-- ffg x with x R p1 
--   where 
--     R : ℕ × ℕ → Set
--     R (zero , zero) = ⊥
--     R (zero , suc m) = ⊤
--     R (suc n , m) = ⊥
--     p1 : Σ (ℕ × ℕ) R
--     fst (fst p1) = zero -- zero
--     snd (fst p1) =  suc zero -- suc zero
--     snd p1 = tt
-- ... | zero , snd₁ = snd₁ 

-- -- BEGIN FIX
-- -- HU: A függvény egy nem üres lista elemeit ciklikusan ismételgeti a végtelenségig.
-- --     Segítség: használjunk where-t vagy subst-ot.
-- -- EN: Repeat a non-empty list cyclicly. When the elements of the list are finished, repeat the same elements in the same order again infinitely.
-- --     Hint: Using where or subst might be helpful.
-- +-suc : ∀ n → n + 1 ≡ suc n
-- +-suc zero    = refl
-- +-suc (suc n) = cong suc (+-suc n)

-- cycle : ∀{i}{A : Set i}{n : ℕ} → Vec A (suc n) → Stream A
-- -- END FIX
-- head (cycle (x ∷ x₁)) = x
-- tail (cycle (x ∷ x₁)) = cycle (rv x x₁) 
--   where
--     same : ∀{i}{A : Set i}{n : ℕ} → Vec A (n + 1)  → Vec A (suc n) 
--     same {i} {A} {n} x = subst (Vec A) (+-suc n) x
--     rv : ∀{i}{A : Set i}{n : ℕ} → A → Vec A n → Vec A (suc n) 
--     rv x v = same (v V.++ (x ∷ []))

-- -- BEGIN FIX
-- test-cycle-1 : S.take 5 (cycle (1 ∷ 2 ∷ 3 ∷ [])) ≡ 1 ∷ 2 ∷ 3 ∷ 1 ∷ 2 ∷ [] {A = ℕ}
-- test-cycle-1 = refl
-- test-cycle-2 : S.take 7 (cycle (1 ∷ 2 ∷ [])) ≡ 1 ∷ 2 ∷ 1 ∷ 2 ∷ 1 ∷ 2 ∷ 1 ∷ [] {A = ℕ}
-- test-cycle-2 = refl
-- test-cycle-3 : S.take 4 (cycle (true ∷ [])) ≡ true ∷ true ∷ true ∷ true ∷ []
-- test-cycle-3 = refl
-- test-cycle-4 : S.take 10 (cycle (10 ∷ 5 ∷ 9 ∷ 2 ∷ [])) ≡ 10 ∷ 5 ∷ 9 ∷ 2 ∷ 10 ∷ 5 ∷ 9 ∷ 2 ∷ 10 ∷ 5 ∷ [] {A = ℕ}
-- test-cycle-4 = refl
-- test-cycle-5 : S.take 11 (cycle (⊤ ∷ ⊥ ∷ ℕ ∷ (ℕ → ℕ) ∷ (ℕ ⊎ Bool) ∷ [])) ≡ ⊤ ∷ ⊥ ∷ ℕ ∷ (ℕ → ℕ) ∷ (ℕ ⊎ Bool) ∷ ⊤ ∷ ⊥ ∷ ℕ ∷ (ℕ → ℕ) ∷ (ℕ ⊎ Bool) ∷ ⊤ ∷ []
-- test-cycle-5 = refl
-- -- END FIX
is<1000 : ℕ → Bool
-- END FIX
is<1000 n = n < 1000
-- BEGIN FIX
test-is<1000-1 : is<1000 1000 ≡ false
test-is<1000-1 = refl
test-is<1000-2 : is<1000 999 ≡ true
test-is<1000-2 = refl
test-is<1000-3 : is<1000 1001 ≡ false
test-is<1000-3 = refl
test-is<1000-4 : is<1000 0 ≡ true
test-is<1000-4 = refl
-- END FIX

-- BEGIN FIX
iso'' : (X Y Z : Set) → (X → (Z × Y)) ↔ ((X → Y ⊎ ⊥) × (X ⊎ ⊥ → Z))
-- END FIX
fst (iso'' X Y Z) x = (λ x₁ → inl (snd (x x₁))) , λ x₁ → case x₁ (λ x₂ → fst (x x₂)) exfalso
snd (iso'' X Y Z) (fst₁ , snd₁) x₁ = (snd₁ (inl x₁)) , (case (fst₁ x₁) id exfalso)

-- BEGIN FIX
fff : (A B : Set) → (A ⊎ B) ↔ Σ Bool (λ b → if b then A else B)
-- END FIX
fst (fff A B) (inl a) = true , a
fst (fff A B) (inr b) = false , b
snd (fff A B) (false , snd₁) = inr snd₁
snd (fff A B) (true , snd₁) = inl snd₁


¬pq : ((P Q : Set) → (¬ P ⊎ Q) ↔ P → P × ¬ Q) ⊎ ¬ ((P Q : Set) → (¬ P ⊎ Q) ↔ P → P × ¬ Q)
-- END FIX
¬pq = inr λ x → snd (x ⊤ ⊤ ((λ x₁ → tt) , (λ x₁ → inr tt))) tt

-- BEGIN FIX

weee₂ : (n k : ℕ) → ((P : ℕ → Set) → P n → P k) ↔ n ≡ k
weee₂ n k = (λ x → x P refl) , λ {refl P₁ x₁ → x₁ }--λ n k → (λ x → {!  x P ? !}) , (λ x P x₁ → {!   !})
-- -- END FIX
-- fst (weee₂ n k) x = x {!   !} {!   !}
-- snd (weee₂ n .n) refl P' x₁ = x₁
  where 
    P : ℕ → Set
    P x = n ≡ x

-- BEGIN FIX
trans≤ : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
-- END FIX
trans≤ x y z (d₁ , snd₁) (d₂ , snd₂) = (d₁ + d₂) , (sym (trans (sym snd₂) (sym (trans (cong (λ a → a + x) (comm+ d₁ d₂)) (trans ( (assoc+ d₂ d₁ x)) ((cong (λ a → d₂ + a) snd₁))))))) --fst x<=y +   fst y<=z , {!   !}
--(cong (λ a → d₂ + a) snd₁) 
p1^ : (n : ℕ) → 1 ^ n ≡ 1
p1^ zero = refl
p1^ (suc n) = trans (idr+ (1 ^ n)) ((p1^ n))

-- BEGIN FIX
suc^ : (n m : ℕ) → Σ ℕ λ k → suc n ^ m ≡ suc k
-- END FIX
suc^ zero zero = zero , refl
suc^ zero (suc m) = zero , (trans (idr+ (1 ^ m)) (p1^ m))
suc^ (suc n) zero = zero , refl
suc^ (suc n) (suc m) with suc^ (suc n) m
... | k , p = {!   !} , {!   !}
--suc n ^ m + n * suc n ^ m = suc k

 {-
 -- ... | (k , p) =  (k + suc (k + n * suc k)) , p1 
--   where
--     p1 : suc (suc n) ^ m + (suc (suc n) ^ m + n * suc (suc n) ^ m) ≡ suc (k + suc (k + n * suc k))
--     p1 = 
--        suc (suc n) ^ m + (suc (suc n) ^ m + n * suc (suc n) ^ m)
--         ≡⟨ cong (λ x → x + ( x +  n * x)) p ⟩
--         suc (k + suc (k + n * suc k)) 
--         ∎
-}       
-- BEGIN FIX
pred2 : Σ ℕ (λ m → m + 3 ≡ 4) ⊎ Σ ℕ (λ m → m + 5 ≡ 2) ⊎ Σ ℕ (λ m → m + 6 ≡ 1)
pred2 = inl (1 , refl)

ineq : ¬ ((a b c : ℕ) → a + b ≤ c ⊎ c + b ≤ a ⊎ a + c ≤ b → c ≤ b ⊎ a ≤ b) -- b is the longest
-- END FIX
ineq x with x 5 2 3
...| y with  y (inr (inl (zero , refl))) 
... | inl (suc (suc zero) , ())
... | inl (suc (suc (suc fst₁)) , ())
... | inr (suc (suc zero) , ())
... | inr (suc (suc (suc fst₁)) , ())

-- BEGIN FIX
-- ffg : ¬ ((R : ℕ × ℕ → Set) → (Σ (ℕ × ℕ) R) → Σ ℕ (λ x → R (x , x)))
-- -- END FIX
-- ffg x with x R' p1 
-- ...| y = {!   !}
--   where 
--     R' : ℕ × ℕ → Set
--     R' (zero , zero) = ⊥
--     R' (zero , suc snd₁) = ⊤
--     R' (suc fst₁ , snd₁) = ⊥
--     p1 : Σ (ℕ × ℕ) R
--     fst p1 = zero , suc zero
--     snd p1 = tt
-- BEGIN FIX
ffg : ¬ ((R : ℕ × ℕ → Set) → (Σ (ℕ × ℕ) R) → Σ ℕ (λ x → R (x , x)))
-- END FIX
ffg x with x R p1 
  where 
    R : ℕ × ℕ → Set
    R (zero , zero) = ⊥
    R (zero , suc m) = ⊤
    R (suc n , m) = ⊥
    p1 : Σ (ℕ × ℕ) R
    fst (fst p1) = zero -- zero
    snd (fst p1) =  suc zero -- suc zero
    snd p1 = tt
... | zero , snd₁ = snd₁ 

-- BEGIN FIX
-- HU: A függvény egy nem üres lista elemeit ciklikusan ismételgeti a végtelenségig.
--     Segítség: használjunk where-t vagy subst-ot.
-- EN: Repeat a non-empty list cyclicly. When the elements of the list are finished, repeat the same elements in the same order again infinitely.
--     Hint: Using where or subst might be helpful.
+-suc : ∀ n → n + 1 ≡ suc n
+-suc zero = refl
+-suc (suc n) = cong suc (+-suc n)

cycle : ∀{i}{A : Set i}{n : ℕ} → Vec A (suc n) → Stream A
-- END FIX
cycle = {!   !}

-- BEGIN FIX
test-cycle-1 : S.take 5 (cycle (1 ∷ 2 ∷ 3 ∷ [])) ≡ 1 ∷ 2 ∷ 3 ∷ 1 ∷ 2 ∷ [] {A = ℕ}
test-cycle-1 = refl
test-cycle-2 : S.take 7 (cycle (1 ∷ 2 ∷ [])) ≡ 1 ∷ 2 ∷ 1 ∷ 2 ∷ 1 ∷ 2 ∷ 1 ∷ [] {A = ℕ}
test-cycle-2 = refl
test-cycle-3 : S.take 4 (cycle (true ∷ [])) ≡ true ∷ true ∷ true ∷ true ∷ []
test-cycle-3 = refl
test-cycle-4 : S.take 10 (cycle (10 ∷ 5 ∷ 9 ∷ 2 ∷ [])) ≡ 10 ∷ 5 ∷ 9 ∷ 2 ∷ 10 ∷ 5 ∷ 9 ∷ 2 ∷ 10 ∷ 5 ∷ [] {A = ℕ}
test-cycle-4 = refl
test-cycle-5 : S.take 11 (cycle (⊤ ∷ ⊥ ∷ ℕ ∷ (ℕ → ℕ) ∷ (ℕ ⊎ Bool) ∷ [])) ≡ ⊤ ∷ ⊥ ∷ ℕ ∷ (ℕ → ℕ) ∷ (ℕ ⊎ Bool) ∷ ⊤ ∷ ⊥ ∷ ℕ ∷ (ℕ → ℕ) ∷ (ℕ ⊎ Bool) ∷ ⊤ ∷ []
test-cycle-5 = refl
-- END FIX
   