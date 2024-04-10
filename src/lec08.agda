{- propositions as types

English            logic     t.t.(Agda)
A and B            A ∧ B     A × B
A or  B            A ∨ B     A ⊎ B
false              ⊥         ⊥ = Empty
true               ⊤         ⊤ = Unit
A implies B        A ⇒ B     A → B
if A, then B       A ⊃ B
not A              ¬ A       A → ⊥
A iff B            A ⇔ B     (A → B) × (B → A)
forall n, P(n)     ∀n.P(n)   (n : X) → P n
exists n, P(n)     ∃n.P(n)   Σ X (λ n → P n) = Σ X P

-}

open import Lib hiding (Eq; _≡_; refl)

-- Even is a predicate on ℕ
Even : ℕ → Set
Even zero = ⊤
Even (suc zero) = ⊥
Even (suc (suc n)) = Even n

Eq : ℕ → ℕ → Set
Eq zero zero = ⊤
Eq (suc n) (suc m) = Eq n m
Eq _ _ = ⊥

Even' : ℕ → Set
Even' n = Σ ℕ λ k → Eq (2 * k) n

Even'' : ℕ → Set
Odd''  : ℕ → Set

Odd'' zero = ⊥
Odd'' (suc n) = Even'' n

Even'' zero = ⊤
Even'' (suc n) = Odd'' n

EvenOdd : ℕ → Set × Set      -- (ℕ → Set) × (ℕ → Set) ≅ (ℕ → Set × Set)  (S^N)*(S^N) = (S^N)^2 = S^(N*2) = S^(2*N) = (S^2)^N = (S*S)^N
EvenOdd zero = (⊤ , ⊥)
-- EvenOdd (suc n) = let (a , b) = EvenOdd n in (b , a)
-- EvenOdd (suc n) = (snd (EvenOdd n) , fst (EvenOdd n))
EvenOdd (suc n) = (snd eo , fst eo)
  where
    eo = EvenOdd n

Even''' : ℕ → Set
Even''' zero = ⊤
Even''' (suc n) = Even''' n → ⊥

-- my proof Agda proof
32isEven : Even 32
32isEven = tt
suceven : (n : ℕ) → Even''' n → ¬ Even''' (suc n)
suceven n e = λ f → f e        -- Church encodings: a = forall b, (a -> b) -> b,   (A → ¬ ¬ A)
32isEven''' : Even''' 32
32isEven''' = λ x → x λ x₁ → {!!}

suceven'' : (n : ℕ) → Even'' n → Odd'' (suc n)
suceven'' n e = e
sucodd'' : (n : ℕ) → Odd'' n → Even'' (suc n)
sucodd'' n e = e
32isEven'' : Even'' 32
32isEven'' = tt

Even''to''' : (n : ℕ) → Even'' n → Even''' n
Odd''to'''  : (n : ℕ) → Odd'' n → ¬ Even''' n
Even''to''' zero e = tt
Even''to''' (suc n) e = Odd''to''' n e
Odd''to''' (suc n) e = λ f → f (Even''to''' n e)

-- first order logical laws

module _ (A : Set)(P Q : A → Set) where
  -- ∀n.(P n ∧ Q n)  ↔   (∀n.P n) ∧ (∀n.Q n)
  ∀× : ((n : A) → (P n × Q n)) ↔ (((n : A) → P n) × ((n : A) → Q n))
  ∀× = {!!}

  -- ∀n.(P n ∨ Q n)  ←   (∀n.P n) ∨ (∀n.Q n), the other is false
  ∀⊎ :  (((n : A) → P n) ⊎ ((n : A) → Q n)) → ((n : A) → (P n ⊎ Q n)) 
  ∀⊎ (inl a) n = inl (a n)
  ∀⊎ (inr b) n = inr (b n)

  -- ∃n.(P n ∧ Q n)   →   (∃n.P n) ∧ (∃n.Q n), the other is false
  ∃× : (Σ A λ n → P n × Q n) → (Σ A P × Σ A Q)
  ∃× = {!!}

  -- ∃n.(P n ∨ Q n)  ↔   (∃n.P n) ∨ (∃n.Q n)
  ∃⊎ :  (Σ A P ⊎ Σ A Q) ↔ (Σ A λ n → P n ⊎ Q n) 
  ∃⊎ = {!!}

notEvenOdd : ((n : ℕ) → Even'' n) ⊎ ((n : ℕ) → Odd'' n) → ⊥
notEvenOdd (inl a) = a 1
notEvenOdd (inr b) = b 0

evenOdd : (n : ℕ) → Even'' n ⊎ Odd'' n
evenOdd zero = inl tt -- : Even'' zero ⊎ Odd'' zero  = ⊤ ⊎ ⊥
evenOdd (suc n) = swap (evenOdd n) -- : Even'' (suc n) ⊎ Odd'' (suc n)  =  Odd'' n ⊎ Even'' n

¬∀⊎ : ¬ ((A : Set)(P Q : A → Set) → ((n : A) → (P n ⊎ Q n))  → (((n : A) → P n) ⊎ ((n : A) → Q n)))
¬∀⊎ H = notEvenOdd (H ℕ Even'' Odd'' evenOdd)

-- equality type

-- data Vec (A : Set) : ℕ → Set
data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

sym' : {A : Set}(a b : A) → a ≡ b → b ≡ a
sym' a .a refl = refl

-- HW: prove that ≡ is transitive and a congruence
