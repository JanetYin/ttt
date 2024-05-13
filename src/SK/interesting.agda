module SK.interesting where
    
open import Lib 


⌜_⌝ : {n : ℕ} → Fin n → ℕ
⌜ fzero ⌝ = 0
⌜ fsuc x ⌝ = suc ⌜ x ⌝

⌞_⌟ : (n : ℕ) → Fin (suc n)
⌞ zero ⌟ = fzero
⌞ suc n ⌟ = fsuc ⌞ n ⌟
safeSubtract : (n : ℕ) → ⦃nonZero : 1 ≥ℕ n⦄ → ℕ → ℕ
safeSubtract n m = n - m
-- Define a function to reverse the order in a Fin set
ind : {n : ℕ} → Fin (suc n) → Fin (suc n)
ind {n} x = ⌞ suc n - 1 - (⌜ x ⌝) ⌟

-- Example usage with specific redefinitions for clarity in how to use ind
example1 : ind {4} (fsuc fzero) ≡ fsuc (fsuc (fsuc fzero))
example1 = refl


interesting : ∀ n m → 2 ^ suc n ≢ 3 ^ suc m
interesting n m x = {!   !}

isEven : ℕ  → Set 
isEven zero = ⊤
isEven (suc zero) = ⊥
isEven (suc (suc x)) = isEven x

isOdd : ℕ  → Set 
isOdd zero = ⊥
isOdd (suc zero) = ⊤
isOdd (suc (suc x)) = isOdd x

pf1 : ∀ n x → isEven (2 ^ suc n) ≡ isEven x
pf1 zero zero = refl
pf1 zero (suc zero) = {!   !}
pf1 zero (suc (suc b)) = {!   !}
pf1 (suc n) b = {!  !}

pf2 : ∀ n → isOdd (3 ^ suc n) 
pf2 = {!   !}

