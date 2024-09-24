-- module en.odd where
open import Data.Nat using (ℕ; suc; zero;_*_;_+_)
open import Relation.Binary.PropositionalEquality using (≡; refl)
-- open import 
-- open import Lib hiding (add; Bool)
Dec : ∀{i}(A : Set i) → Set i
Dec A = A ⊎ (A → ⊥)


data Parity : ℕ → Set where
  even : (k : ℕ) → Parity      (k * 2)
  odd  : (k : ℕ) → Parity (1 + (k * 2))

parity : (n : ℕ) → Parity n
parity zero        = even zero
parity (suc n)   with n | parity n
... |     .(k * 2) | even k = odd       k
... | .(1 + k * 2) | odd  k = even (suc k)

data Bool : Set where
  true  : Bool
  false : Bool

isEven : ( n : ℕ ) → Bool
isEven n
  with parity n
... | (even k)  = true
... | (odd k)  = false

isOdd : ( n : ℕ ) → Bool
isOdd n
  with parity n
... | (even k)  = false
... | (odd k)   = true

half : ℕ → ℕ
half n
  with parity n
... | even k = k
... | odd  k = k

data _≡parity_ : ℕ → ℕ → Set where
  bothEven : ∀ k l → (0 + (k * 2)) ≡parity (0 + (l * 2))
  bothOdd  : ∀ k l → (1 + (k * 2)) ≡parity (1 + (l * 2))

≡parity-reflexive : ∀ {n} → n ≡parity n
≡parity-reflexive {n} with parity n
... | even k = bothEven k k
... | odd k = bothOdd  k k

≡parity-commutative : ∀ {m n} → m ≡parity n → n ≡parity m
≡parity-commutative (bothEven k l) = bothEven l k
≡parity-commutative (bothOdd k l)  = bothOdd l k

≡parity-even0 : ∀ {m} → (m * 2) ≡parity zero
≡parity-even0 {zero} = ≡parity-reflexive {zero}
≡parity-even0 {suc m} = bothEven  (suc m) 0 
≡parity-transitive : ∀ {m n k} → m ≡parity n → n ≡parity k → m ≡parity k
≡parity-transitive {.(0 + k₁ * 2)} {.(0 + l * 2)} {zero} (bothEven k₁ l) x₁ = ≡parity-even0 {k₁}
≡parity-transitive {.(0 + k₁ * 2)} {.(0 + l * 2)} {suc k} (bothEven k₁ l) x₁ = {!   !}
≡parity-transitive {.(1 + k₁ * 2)} {.(1 + l * 2)} {k} (bothOdd k₁ l) x₁ = {!   !}
 


odd-even-diff-parity : ∀ {m n} → Dec (m * 2 ≡parity n)
odd-even-diff-parity = ?

≡parity-transitive₁ : ∀ {m n k} → m ≡parity n → n ≡parity k → m ≡parity k
≡parity-transitive₁ {.(0 + k₁ * 2)} {.(0 + l * 2)} {k} (bothEven k₁ l) x₁ with parity k 
... | even k = bothEven k₁ k
... | odd k = {! x₁ !} 
≡parity-transitive₁ {.(1 + k₁ * 2)} {.(1 + l * 2)} {k} (bothOdd k₁ l) x₁ with parity k 
... | even k = {!   !}
... | odd k = bothOdd k₁ k 