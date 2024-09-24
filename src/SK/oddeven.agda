open import Lib hiding (_$_;_$'_;proj;_<_)

{- Helped by Viktor -}
module SK.oddeven where


Even' Odd' : ℕ → Set
Even' zero = ⊤
Even' (suc x) = Odd' x
Odd' zero = ⊥
Odd' (suc x) = Even' x

evenOddImpossible : ∀ n → Even' n → Odd' n → ⊥
evenOddImpossible (suc n) e o = evenOddImpossible n o e

data Parity : ℕ → Set where
  even : (k : ℕ) → Parity      (k * 2)
  odd  : (k : ℕ) → Parity (1 + (k * 2))

parity : (n : ℕ) → Parity n
parity zero        = even zero
parity (suc n)   with n | parity n
... |     .(k * 2) | even k = odd       k
... | .(1 + k * 2) | odd  k = even (suc k)


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

≡parity-odd1 : ∀ {m} → (1 + m * 2) ≡parity (suc zero)
≡parity-odd1 {zero} = ≡parity-reflexive {suc zero}
≡parity-odd1 {suc m} = bothOdd  (suc m) 0

≡parity-even0 : ∀ {m} → (m * 2) ≡parity zero
≡parity-even0 {zero} = ≡parity-reflexive {zero}
≡parity-even0 {suc m} = bothEven  (suc m) 0 
≡parity-transitive : ∀ {m n k} → m ≡parity n → n ≡parity k → m ≡parity k
≡parity-transitive {.(0 + k₁ * 2)} {.(0 + l * 2)} {zero} (bothEven k₁ l) x₁ = ≡parity-even0 {k₁}
≡parity-transitive {.(0 + k₁ * 2)} {.(0 + l * 2)} {suc k} (bothEven k₁ l) x₁ = {!   !}
≡parity-transitive {.(1 + k₁ * 2)} {.(1 + l * 2)} {k} (bothOdd k₁ l) x₁ = {!   !}
-- p1 : k₁ * 2 ≟ suc (k₂ * 2)
--suc-injective≡ℕ
bot1 : ∀ {l k} → k ≡ 2 → l ≡ 1 → k ≡parity l → ⊥
bot1 x () (bothEven (suc k) zero)
bot1 x () (bothEven (suc k) (suc l)) --suc-injective≡ℕ x₁ --suc-injective≡ℕ x₁
bot1 () x₁ (bothOdd zero zero)
bot1 () x₁ (bothOdd (suc k) zero)  --() --{!   !}


≡parity-evenodd : ∀ {m k} → (m * 2) ≡parity suc (k * 2) → ⊥
≡parity-evenodd {zero} {zero} x with parity 0 
...| y = {!  !}
≡parity-evenodd {zero} {suc k} x = {!   !}
≡parity-evenodd {suc m} {zero} x = {!   !}
≡parity-evenodd {suc m} {suc k} x = {!   !}
odd-even-diff-parity : ∀ {m n} → Dec ((m * 2) ≡parity n) -- (m * 2 ≡parity n)
odd-even-diff-parity {m} {n} with parity n 
... | even k = inl (bothEven m k)
... | odd k = inr (λ x → {! !})

≡parity-transitive₁ : ∀ {m n k} → m ≡parity n → n ≡parity k → m ≡parity k
≡parity-transitive₁ {.(0 + k₁ * 2)} {.(0 + l * 2)} {k} (bothEven k₁ l) x₁ with parity k 
... | even k = bothEven k₁ k
... | odd k = {!   !}
≡parity-transitive₁ {.(1 + k₁ * 2)} {.(1 + l * 2)} {k} (bothOdd k₁ l) x₁ with parity k 
... | even k = {!   !}        
... | odd k = bothOdd k₁ k

data SameParity (k l : ℕ) : Set where
  even2 : Even' k → Even' l → SameParity k l
  odd2 : Odd' k → Odd' l → SameParity k l

sameParity-refl : ∀ n → SameParity n n
sameParity-refl zero = even2 tt tt
sameParity-refl (suc zero) = odd2 tt tt 
sameParity-refl (suc (suc n)) with sameParity-refl n
... | even2 x x₁ = even2 x x₁
... | odd2 x x₁ = odd2 x x₁

sameParity+2-left : ∀ n m → SameParity n m → SameParity (2 + n) m
sameParity+2-left n m (even2 x x₁) = even2 x x₁
sameParity+2-left n m (odd2 x x₁) = odd2 x x₁

sameParity+2-right : ∀ n m → SameParity n m → SameParity n (2 + m)
sameParity+2-right n m (even2 x x₁) = even2 x x₁
sameParity+2-right n m (odd2 x x₁) = odd2 x x₁

sameParity-sym : ∀ n m → SameParity n m → SameParity m n
sameParity-sym n m (even2 x x₁) = even2 x₁ x
sameParity-sym n m (odd2 x x₁) = odd2 x₁ x

sameParity-transitive : ∀ n m k → SameParity n m → SameParity m k → SameParity n k
sameParity-transitive n m k (even2 x x₁) (even2 x₂ x₃) = even2 x x₃
sameParity-transitive n m k (even2 x x₁) (odd2 x₂ x₃) = exfalso (evenOddImpossible m x₁ x₂)
sameParity-transitive n m k (odd2 x x₁) (even2 x₂ x₃) = exfalso (evenOddImpossible m x₂ x₁)
sameParity-transitive n m k (odd2 x x₁) (odd2 x₂ x₃) = odd2 x x₃ 

sum : (n : ℕ)  → ℕ 
sum zero = zero
sum (suc n) = (suc n) + (sum n)

p1 : ∀ {a b : ℕ} →  a + (suc b) ≡ suc (a + b)
p1 {zero} {b} = refl
p1 {suc a} {b} = cong suc (p1 {a} {b})

-- sum (suc n) = (suc n) + (sum n)
p2 : ∀ {n m} → n * (suc m) ≡ n + (n * m)
p2 {zero} {m} = refl
p2 {suc n} {m} = cong suc (sym (trans (comm+ n (m + n * m)) (trans (assoc+ m (n * m) n) (cong (m +_) (trans (comm+  (n * m) n) (sym (p2 {n} {m})))))))
lem' : ∀ {n} → 2 * sum n ≡ n * (n + 1)
lem' {zero} = refl   
lem' {suc n} = cong suc (trans (assoc+ n (sum n) (suc (n + sum n + zero))) (sym (trans (assoc+ n 1 (n * suc (n + 1))) (cong (n +_) (sym (trans (p1 {sum n} {n + sum n + zero}) (cong suc (sym (trans (p2 {n} {(n + 1)}) (sym (trans (comm+ (sum n) (n + sum n + zero)) (trans (p3 {n}) (cong (n +_) (lem' {n})))))))))))))) 
  where
    p3 : ∀ {n} →  n + sum n + zero + sum n ≡ n + (2 * sum n)
    p3 {n} = {!   !} 