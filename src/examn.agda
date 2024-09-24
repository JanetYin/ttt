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
-- HU: A szám 1000-e?
-- EN: Does the number equal to 1000?
is1000 : ℕ → Bool
-- END FIX
is1000 x = (x == 1000)
-- BEGIN FIX
test-is1000-1 : is1000 1000 ≡ true
test-is1000-1 = refl
test-is1000-2 : is1000 999 ≡ false
test-is1000-2 = refl
test-is1000-3 : is1000 1001 ≡ false
test-is1000-3 = refl
test-is1000-4 : is1000 0 ≡ false
test-is1000-4 = refl
-- END FIX
p2 : ℕ → ℕ ⊎ ℕ
p2 zero = inl zero
p2 (suc zero) = inr zero
p2 (suc (suc x)) = case (p2 x) (λ x₁ → inl (suc x₁)) λ x₁ → inr (suc x₁)
-- p2 (suc zero) = inr zero
-- p2 (suc (suc zero)) = inl 1
-- p2 (suc (suc (suc zero))) = inl 3
-- p2 (suc (suc (suc (suc x)))) = {!  inl n !}
-- 0 inl zero
-- 1 inr zero 
-- 2 inl 1
-- 3 inr 1 

-- BEGIN FIX
-- HU: Bizonyítsuk, hogy ℕ izomorf ℕ ⊎ ℕ-nel.
-- EN: Prove that ℕ is isomorphic to ℕ ⊎ ℕ.
ℕ=2ℕ : ℕ ↔ ℕ ⊎ ℕ
-- END FIX
fst ℕ=2ℕ x = p2 x
snd ℕ=2ℕ (inl zero) = zero
snd ℕ=2ℕ (inl (suc a)) = 2 * (suc a)
snd ℕ=2ℕ (inr zero) = 1
snd ℕ=2ℕ (inr (suc b)) = 2 * (suc b) + 1 -- case x (λ x₁ → x₁) λ x₁ → x₁
-- BEGIN FIX
test-ℕ=2ℕ-1 : snd ℕ=2ℕ (fst ℕ=2ℕ 3) ≡ 3
test-ℕ=2ℕ-1 = refl
test-ℕ=2ℕ-2 : snd ℕ=2ℕ (fst ℕ=2ℕ 10) ≡ 10
test-ℕ=2ℕ-2 = refl
test-ℕ=2ℕ-3 : snd ℕ=2ℕ (fst ℕ=2ℕ 0) ≡ 0
test-ℕ=2ℕ-3 = refl
test-ℕ=2ℕ-4 : snd ℕ=2ℕ (fst ℕ=2ℕ 15) ≡ 15
test-ℕ=2ℕ-4 = refl
test-ℕ=2ℕ-5 : snd ℕ=2ℕ (fst ℕ=2ℕ 18) ≡ 18
test-ℕ=2ℕ-5 = refl
test-ℕ=2ℕ-6 : fst ℕ=2ℕ (snd ℕ=2ℕ (inl 3)) ≡ inl 3
test-ℕ=2ℕ-6 = refl
test-ℕ=2ℕ-7 : fst ℕ=2ℕ (snd ℕ=2ℕ (inl 6)) ≡ inl 6
test-ℕ=2ℕ-7 = refl
test-ℕ=2ℕ-8 : fst ℕ=2ℕ (snd ℕ=2ℕ (inr 10)) ≡ inr 10
test-ℕ=2ℕ-8 = refl
test-ℕ=2ℕ-9 : fst ℕ=2ℕ (snd ℕ=2ℕ (inr 15)) ≡ inr 15
test-ℕ=2ℕ-9 = refl
-- END FIX

p1 : ∀ {x} → Vec ⊤ x 
p1 {zero} = []
p1 {suc x} = tt ∷ (p1 {x})
-- BEGIN FIX
vecℕ⊤ : ℕ ↔ Σ ℕ (Vec ⊤)
-- END FIX
fst vecℕ⊤ x = x , p1
snd vecℕ⊤ x = fst x
    
-- BEGIN FIX
test-vecℕ⊤-1 : snd vecℕ⊤ (fst vecℕ⊤ 1) ≡ 1
test-vecℕ⊤-1 = refl
test-vecℕ⊤-2 : snd vecℕ⊤ (fst vecℕ⊤ 3) ≡ 3
test-vecℕ⊤-2 = refl
test-vecℕ⊤-3 : snd vecℕ⊤ (fst vecℕ⊤ 7) ≡ 7
test-vecℕ⊤-3 = refl
test-vecℕ⊤-4 : fst vecℕ⊤ (snd vecℕ⊤ (3 , tt ∷ tt ∷ tt ∷ [])) ≡ (3 , tt ∷ tt ∷ tt ∷ [])
test-vecℕ⊤-4 = refl
test-vecℕ⊤-5 : fst vecℕ⊤ (snd vecℕ⊤ (5 , tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])) ≡ (5 , tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
test-vecℕ⊤-5 = refl
test-vecℕ⊤-6 : fst vecℕ⊤ (snd vecℕ⊤ (6 , tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])) ≡ (6 , tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
test-vecℕ⊤-6 = refl
-- END FIX


-- BEGIN FIX
phantom : (F : Set → Set) → ((A B : Set) → (A → B) → F A → F B) → ((A B : Set) → (A → B) → F B → F A) → ((A B : Set) → F A → F B)
-- END FIX
phantom  F x x₁ A B a = x₁ (B) (B → B) (λ x₂ x₃ → x₂) ((x (B → A ) (B → B) (λ c b₁ → b₁)  (x (A) (B → A) (λ a b → a) a ))) --x (A → B) B (λ x₂ → x₂ {!   !}) {!   (x₁ (A → B) A  ? a)  !} --{!  subst !} --x₁ B A {!   !} x₂
--F (B → A) (x (A) (B → A) (λ a b → a) a ) 
--F (B → B) x (B → A ) (B → B) (λ c b₁ → b₁)  (x (A) (B → A) (λ a b → a) a )
--F (A → B)  (x₁ (A → B) A  ? a)
-- BEGIN FIX
ffaa : (x : ℕ) → Σ ℕ λ y → x ≡ 1 * x
-- END FIX
ffaa x = 10 , (sym (idr+ x))


-- BEGIN FIX
≤n+ : (x y n : ℕ) → x ≤ y → x ≤ n + y
-- END FIX
≤n+ x y n (a , a+x≡y) = (n + a) , (trans ( (assoc+ n a x)) (cong (n +_) a+x≡y))

+-suc : ∀ n → n + 1 ≡ suc n
+-suc zero = refl
+-suc (suc n) = (cong suc (+-suc n))
  where
    suc-inj : ∀ {n k} → suc n ≡ suc k → n ≡ k 
    suc-inj refl = refl
+1inj : ∀ {a b} → a ≡ b → suc a ≡ suc b 
+1inj refl = cong suc refl
+-suc2 : ∀ {n x} → suc (n + suc x) ≡ n + suc (suc x)
+-suc2 {zero} {x} = refl
+-suc2 {suc n} {x} = cong suc (+-suc2 {n} {x})
inj' : ∀ {x y n} → n + x ≡ y → n + suc x ≡ suc y 
inj' {zero} {y} {n} x₁ = sym (trans (sym (+1inj x₁)) (sym (trans (+-suc n) (cong suc (sym (idr+ n))))))
inj' {suc x} {y} {n} x₁ = sym (trans (sym (+1inj x₁)) +-suc2) 

suc+ : ∀ {n x} → n + suc x ≡ suc (n + x)
suc+ {zero} {x} = refl
suc+ {suc n} {x} = cong suc (suc+ {n} {x})

inj3 : ∀ {n x y } → n + suc x ≡ suc y → n + x ≡ y
inj3 {zero} {x} {.x} refl = refl
inj3 {suc n} {x} {.(n + suc x)} refl = sym (suc+ {n} {x})
-- BEGIN FIX
dec≤ℕ : (x y : ℕ) → x ≤ y ⊎ ¬ (x ≤ y)
-- END FIX
dec≤ℕ zero y = inl (y , (idr+ y))
dec≤ℕ (suc x) zero = inr (λ {(zero , ())
                           ; (suc fst₁ , ())})
dec≤ℕ (suc x) (suc y) with dec≤ℕ x y 
... | inl a = inl (fst a , inj' (snd a))
... | inr b = inr (λ {(n , snd₁) → b (n , inj3 snd₁)})

-- BEGIN FIX
noℕsqrt : ¬ ((n k : ℕ) → Σ ℕ λ m → m * m ≡ n * k)
-- END FIX
noℕsqrt x with x 1 2 
... | suc (suc zero) , ()
... | suc (suc (suc fst₁)) , ()

-- BEGIN FIX
¬¬∃↓ : ¬ ((f : ℕ → ℕ) → Σ ℕ λ n → (k : ℕ) → suc (f n) ≤ (f k))
-- END FIX
¬¬∃↓ x with x id 
... | fst₁ , snd₁ with snd₁ 0
¬¬∃↓ x | zero , snd₁ | zero , ()
¬¬∃↓ x | zero , snd₁ | suc fst₂ , ()
¬¬∃↓ x | suc fst₁ , snd₁ | zero , ()
¬¬∃↓ x | suc fst₁ , snd₁ | suc fst₂ , ()

-- BEGIN FIX
-- HU: A függvény egy végtelen lista (Stream) minden második elemét elhagyja!
--     (Az elsőt megtartja, másodikat eldobja, harmadikat megtartja, stb.)
-- EN: Drop every second element of a Stream. (Keeps the first, drops second, keeps third, drops fourth, and so on...)
halfStream : ∀{i}{A : Set i} → Stream A → Stream A
-- END FIX
head (halfStream x) = head x --- 0 1 2 3 tail 2 3
-- head (tail (halfStream x)) = head (tail (tail (halfStream x)) )
tail (halfStream x) = halfStream (tail (tail x)) 
-- BEGIN FIX
test-halfStream-1 : S.take 10 (halfStream (S.iterate suc 0)) ≡ 0 ∷ 2 ∷ 4 ∷ 6 ∷ 8 ∷ 10 ∷ 12 ∷ 14 ∷ 16 ∷ 18 ∷ []
test-halfStream-1 = refl
test-halfStream-2 : S.take 6 (halfStream (S.iterate (λ x → if x then false else true) true)) ≡
  true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ []
test-halfStream-2 = refl
test-halfStream-3 : S.take 8 (halfStream (S.map (λ x → x * x) (S.iterate suc 0))) ≡
  0 ∷ 4 ∷ 16 ∷ 36 ∷ 64 ∷ 100 ∷ 144 ∷ 196 ∷ []
test-halfStream-3 = refl
-- END FIX
 
   